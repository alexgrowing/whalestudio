import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.AdelicInclusionThirdIdempotent
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.AvgEqOfIsAv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Cusp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEnd.Grp PositivityTheory.ThKEnd.Two

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d j : ℕ}
  {W : Spc F E d} {u u' : Matrix (Fin d) (Fin j) E}

open GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic

variable (σ W) in

structure Ctx : Prop where
  cm : IsCMExt F E σ
  skew : ∀ i j, σ (W.J j i) = -W.J i j
  det : W.J.det ≠ 0

instance lcUA : LocallyCompactSpace (UA σ W.J) := (GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ d W.J).2.1
instance scUA : SecondCountableTopology (UA σ W.J) := (GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ d W.J).2.2.1
instance fcUA : FirstCountableTopology (UA σ W.J) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ scUA
instance t2UA : T2Space (UA σ W.J) := inferInstance
instance cntU : Countable (ratU σ W.J) := PositivityTheory.ThKF.countable_ratU σ W.J

theorem Ctx.disc (C : Ctx σ W) : DiscreteTopology (ratU σ W.J) :=
  PositivityTheory.ThKF.discrete_ratU C.cm (ε := -1) (fun i j => by simp [C.skew]) C.det

theorem Ctx.good (C : Ctx σ W) (U : Submodule E (Fin d → E)) : UnipGood (unipU σ W U) :=
  (unipUGood F E σ C.cm d W (Or.inr C.skew) C.det U).1

theorem Ctx.lat (C : Ctx σ W) (U : Submodule E (Fin d → E)) : Lat ((ratU σ W.J).subgroupOf (unipU σ W U)) := by
  have := C.disc
  let i : (ratU σ W.J).subgroupOf (unipU σ W U) → ratU σ W.J := fun x => ⟨x.1.1, x.2⟩
  have ii : Function.Injective i := fun a b h => Subtype.ext (Subtype.ext (congrArg Subtype.val h :))
  exact ⟨ii.countable, DiscreteTopology.of_continuous_injective
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) ii, (C.good U).cov⟩

variable (σ W) in

abbrev Av (U : Submodule E (Fin d → E)) (f c : UA σ W.J → ℂ) : Prop :=
  IsAv ((ratU σ W.J).subgroupOf (unipU σ W U)) (fun a => a.1) f c

theorem isAv_left {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] {Γ : Subgroup G} [Group H] {ι : G →* H} {f c : H → ℂ}
    (L : Lat Γ) (h : IsAv Γ ι f c) (n : G) (x : H) : c (ι n * x) = c x := by
  have := L.cnt
  obtain ⟨μ, 𝓕, h1, h2, h3, h4⟩ := L.pair
  have := L.right μ
  have fd : IsFundamentalDomain Γ 𝓕 μ := .mk' h2.nullMeasurableSet h3
  have mp := measurePreserving_mul_right μ n
  have h5 : IsFundamentalDomain Γ ((Equiv.mulRight n) ⁻¹' 𝓕) μ :=
    fd.preimage_of_equiv mp.quasiMeasurePreserving Function.bijective_id fun γ x => by
      change _ * x * n = _ * (x * n)
      rw [mul_assoc]; rfl
  rw [h μ _ h1 h5 ((mp.measure_preimage h2.nullMeasurableSet).trans h4), h μ 𝓕 h1 fd h4,
    ← mp.setIntegral_preimage_emb (measurableEmbedding_mulRight n) _ 𝓕]
  simp only [map_mul, mul_assoc]
  rfl

def conjE {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B : Subgroup G} (γ : G)
    (h : ∀ s ∈ A, γ * s * γ⁻¹ ∈ B) (h' : ∀ s ∈ B, γ⁻¹ * s * γ ∈ A) : A ≃ₜ* B where
  toFun s := ⟨_, h s s.2⟩
  invFun s := ⟨_, h' s s.2⟩
  left_inv s := Subtype.ext (by simp [mul_assoc])
  right_inv s := Subtype.ext (by simp [mul_assoc])
  map_mul' s t := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  continuous_invFun := Continuous.subtype_mk (by fun_prop) _

theorem conj_rat {G : Type} [Group G] {Γ : Subgroup G} {γ : G} (hγ : γ ∈ Γ) (s : G) : γ * s * γ⁻¹ ∈ Γ ↔ s ∈ Γ := by
  rw [Subgroup.mul_mem_cancel_right _ (inv_mem hγ), Subgroup.mul_mem_cancel_left _ hγ]

structure IsCt (U : Submodule E (Fin d → E)) (ct : (UA σ W.J → ℂ) → UA σ W.J → ℂ) : Prop where
  smul : ∀ (c : ℂ) f, ct (c • f) = fun x => c * ct f x
  right : ∀ f k, ct (fun y => f (y * k)) = fun x => ct f (x * k)
  add : ∀ f f', IsAut (W := W) f → IsAut (W := W) f' → ct (f + f') = fun x => ct f x + ct f' x
  av : ∀ f, IsAut (W := W) f → Av σ W U f (ct f)

theorem Ctx.ct (C : Ctx σ W) (U : Submodule E (Fin d → E)) : ∃ ct, IsCt (σ := σ) (W := W) U ct := by
  have := (C.good U).lc
  have := (C.good U).sc
  obtain ⟨lam, h1, h2⟩ := (C.lat U).isAv_prob (H := UA σ W.J)
  have i : ∀ f, IsAut (W := W) f → ∀ x, Integrable (fun u : unipU σ W U => f (u.1 * x)) lam := fun f hf x => by
    obtain ⟨M, hM⟩ := (C.lat U).bound (ι := Subgroup.subtype _) continuous_subtype_val hf.1 (fun γ h => hf.2 _ h)
      (isCompact_singleton (x := x))
    have := hf.1
    exact .of_bound (Continuous.aestronglyMeasurable (by fun_prop)) M (.of_forall fun u => hM u _ rfl)
  refine ⟨fun f x => ∫ u, f (u.1 * x) ∂lam, fun c f => funext fun x => integral_const_mul _ _, fun f k => by simp only [mul_assoc],
    fun f f' a b => funext fun x => integral_add (i f a x) (i f' b x), fun f hf => ?_⟩
  obtain ⟨c, hc⟩ := (C.lat U).isAv_ex (ι := Subgroup.subtype _) (f := f) fun γ h => hf.2 _ h
  exact (funext (h2 _ f c hc) :) ▸ hc

def th (C : Ctx σ W) (j : ℕ) : GA E j →* GL (Fin j) (AE F E) :=
  Matrix.GeneralLinearGroup.map (GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv C.cm).symm.toRingHom

abbrev Ctx.ad (C : Ctx σ W) : AE F E ≃+* Ad E := GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv C.cm

theorem Ctx.ad_inc (C : Ctx σ W) (x : E) : C.ad (inclR (F := F) (AF F) x) = algebraMap E _ x :=
  GlobalTheory.UnitaryHeckeBaseChange.toAdele_incA x

theorem Ctx.ad_cont (C : Ctx σ W) : Continuous C.ad := GlobalTheory.UnitaryHeckeBaseChange.continuous_toAdele F E

theorem th_cont (C : Ctx σ W) : Continuous (th C j) := by
  have c := GlobalTheory.UnitaryHeckeBaseChange.continuous_adeleEquiv_symm C.cm
  exact Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map c, Units.continuous_coe_inv.matrix_map c⟩

theorem th_rat (C : Ctx σ W) (γ : GL (Fin j) E) : th C j (ratGL E j γ) = Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) γ :=
  Units.ext (Matrix.ext fun a b => C.ad.symm_apply_eq.2 (C.ad_inc _).symm)

variable (C : Ctx σ W) (h : Fr (σ : E →+* E) W.J u u') {ct : (UA σ W.J → ℂ) → UA σ W.J → ℂ} (H : IsCt (colSp u) ct)
  {f : UA σ W.J → ℂ} (hf : IsAut (W := W) f)
include C h H hf

omit h in
theorem ct_cont : Continuous (ct f) := by
  have := (C.good (colSp u)).lc
  have := (C.good (colSp u)).sc
  exact IsAv.cont (ι := Subgroup.subtype _) (C.lat _) (H.av f hf) continuous_subtype_val hf.1 fun γ h => hf.2 _ h

omit h in
theorem ct_left {n : UA σ W.J} (hn : n ∈ unipU σ W (colSp u)) (x) : ct f (n * x) = ct f x := by
  have := (C.good (colSp u)).lc
  have := (C.good (colSp u)).sc
  exact isAv_left (ι := Subgroup.subtype _) (C.lat _) (H.av f hf) ⟨n, hn⟩ x

theorem ct_rat (γ : GL (Fin j) E) (x) : ct f (lev h (th C j (ratGL E j γ)) * x) = ct f x := by
  have := (C.good (colSp u)).lc
  have := (C.good (colSp u)).sc
  rw [th_rat]
  have r := lev_rat (F := F) h γ
  set g := Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) γ
  refine IsAv.conj (ι := Subgroup.subtype _) (C.lat _) (H.av f hf) (conjE (lev h g)⁻¹ (fun s hs => by simpa using lev_norm h g⁻¹ s hs)
    fun s hs => by simpa using lev_norm h g s hs) (fun s => conj_rat (inv_mem r) s.1) (fun s => ?_) (hf.2 _ r) x
  change s.1 * _ = _ * (_ * s.1 * _)
  simp [mul_assoc]

theorem ct_pre {ψ : AddChar (Ad E) ℂ} (x) : Pre ψ (j - 1) fun g => ct f (lev h (th C j g) * x) :=
  pre_top ((ct_cont C H hf).comp ((((isLev h).1.comp (th_cont C))).mul continuous_const)) fun γ g => by
    rw [map_mul, map_mul, mul_assoc, ct_rat C h H hf]

def fst {R : Type} (u : Matrix (Fin d) (Fin j) R) {r : ℕ} (hr : r ≤ j) : Matrix (Fin d) (Fin r) R := u.submatrix id (Fin.castLE hr)

omit C H hf in
theorem fr_fst {r : ℕ} (hr : r ≤ j) : Fr (σ : E →+* E) W.J (fst u hr) (fst u' hr) := by
  have k : ∀ a b : Matrix (Fin d) (Fin j) E, (fst a hr)ᵀ * W.J * (fst b hr).map (σ : E →+* E) =
      (aᵀ * W.J * b.map (σ : E →+* E)).submatrix (Fin.castLE hr) (Fin.castLE hr) := fun a b => rfl
  exact ⟨h.cc, h.sk, by rw [k, h.uu]; rfl, by rw [k, h.vv]; rfl, by rw [k, h.uv, Matrix.submatrix_one _ (Fin.castLE_injective hr)]⟩

omit C H hf in
theorem mid_mat {s t : UA σ W.J} (a : mat s * incM F u = incM F u) (b : mat t⁻¹ * incM F u = incM F u) :
    mid (cR σ) (incM F W.J) (incM F u) (incM F u') (mat (s * t)) =
      mid (cR σ) (incM F W.J) (incM F u) (incM F u') (mat s) * mid (cR σ) (incM F W.J) (incM F u) (incM F u') (mat t) := by
  have := (frA h).row_mul (adj_mat t) (g := 1) (by rw [Matrix.mul_one, b])
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul] at this
  rw [mat_mul, (frA h).mid_mul (by rw [e1, ← Matrix.mul_assoc, a]) (by rw [e3, Matrix.neg_mul, Matrix.mul_assoc, this])]

theorem ct_van {r : ℕ} (hr : r ≤ j - 1) (h0 : Av σ W (colSp (fst u (hr.trans (Nat.sub_le j 1)))) f 0) (x) :
    avg (ratV E (UnipotentBlockColumnIndex j r (j - 1))) (fun y => ct f (lev h (th C j (blkU y)) * x)) = 0 := by
  have hr' := hr.trans (Nat.sub_le j 1)
  have h₁ := fr_fst h hr'
  have := C.disc
  letI : MeasurableSpace (Multiplicative (UnipotentBlockColumnIndex j r (j - 1) → Ad E)) := borel _
  haveI : BorelSpace (Multiplicative (UnipotentBlockColumnIndex j r (j - 1) → Ad E)) := ⟨rfl⟩
  let β : Multiplicative (UnipotentBlockColumnIndex j r (j - 1) → Ad E) →* GA E j := MonoidHom.mk' (fun y => blkU y.toAdd) fun a b => posU_add _ _ _
  let ι := (lev h).comp ((th C j).comp β)
  have cι : Continuous ι := (isLev h).1.comp ((th_cont C).comp (continuous_posU (isNil_blk j r (j - 1))))
  let π : UA σ W.J → Multiplicative (UnipotentBlockColumnIndex j r (j - 1) → Ad E) := fun s => Multiplicative.ofAdd fun t =>
    C.ad ((row (cR σ) (incM F W.J) (incM F u') * mat s * incM F u) t.1.1 t.1.2)
  have cπ : Continuous π := continuous_pi fun t => C.ad_cont.comp
    (((continuous_const.matrix_mul continuous_mat).matrix_mul continuous_const).matrix_elem _ _)
  have ιu : ∀ b, mat (ι b) * incM F u = incM F u * (1 + posM Subtype.val b.toAdd).map C.ad.symm := fun b => (frA h).lv_u _ _
  have LB := lat_mult (isCoLat_ratV E (UnipotentBlockColumnIndex j r (j - 1)))
  have r1 : ∀ b ∈ (ratV E (UnipotentBlockColumnIndex j r (j - 1))).toSubgroup, ι b ∈ ratU σ W.J := by
    rintro _ ⟨c, rfl⟩
    have := lev_rat (F := F) h (blkU c)
    rwa [← th_rat C, ratGL_blkU] at this
  obtain ⟨s1, s2, s3⟩ := prod_stage (Γ := ratU σ W.J) (C.good (colSp u)).closed (C.lat _) LB cι (fun b => lev_norm h _) π cπ
    (fun a ha b => funext fun t => by
      change C.ad _ = b.toAdd t
      rw [mat_mul, Matrix.mul_assoc, Matrix.mul_assoc, ιu, ← Matrix.mul_assoc (mat a), ((mem_N h).1 ha).1, ← Matrix.mul_assoc,
        (frA h).vu, Matrix.one_mul, Matrix.map_apply, RingEquiv.apply_symm_apply, Matrix.add_apply, posM_blk_apply, dif_pos t.2,
        Matrix.one_apply_ne (fun e => by have := t.2; rw [e] at this; omega), zero_add]) r1
    (fun γ hγ => by
      obtain ⟨g, -, hg, -⟩ := mem_ratU.1 hγ
      refine ⟨fun t => (row (σ : E →+* E) W.J u' * g * u) t.1.1 t.1.2, funext fun t => ?_⟩
      change algebraMap E _ _ = C.ad _
      rw [hg, ← incM_row, ← incM_mul, ← incM_mul, ← C.ad_inc]; rfl)
  set S := prodG (unipU σ W (colSp u)) ι fun b => lev_norm h _
  have fix : ∀ s : S, mat s.1 * incM F (fst u hr') = incM F (fst u hr') := by
    rintro ⟨s, b, hb⟩
    have e : mat s * incM F u = incM F u * (1 + posM Subtype.val b.toAdd).map C.ad.symm := by
      conv_lhs => rw [← inv_mul_cancel_right s (ι b), mat_mul, Matrix.mul_assoc, ιu, ← Matrix.mul_assoc, ((mem_N h).1 hb).1]
    ext a k
    refine (congrFun (congrFun e a) (Fin.castLE hr' k)).trans ?_
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE hr' k) (fun l _ hl => ?_) (by simp)]
    all_goals rw [Matrix.map_apply, Matrix.add_apply, posM_blk_apply, dif_neg (fun q => by have := k.2; simp at q; omega), add_zero]
    · simp [fst, incM]
    · rw [Matrix.one_apply_ne hl, map_zero, mul_zero]
  have le : unipU σ W (colSp (fst u hr')) ≤ S := fun n hn => by
    obtain ⟨a, b⟩ := (mem_N h₁).1 hn
    have mv := congrArg (· * incM F u) ((frA h₁).move (adj_mat n) a ((mem_N h₁).1 (inv_mem hn)).1 b)
    have e3u : (1 - e3 (cR σ) (incM F W.J) (incM F (fst u hr')) (incM F (fst u' hr'))) * incM F u = incM F u := by
      rw [Matrix.sub_mul, e3, Matrix.neg_mul, Matrix.mul_assoc, show row (cR σ) (incM F W.J) (incM F (fst u hr')) * incM F u =
        (row (cR σ) (incM F W.J) (incM F u) * incM F u).submatrix (Fin.castLE hr') id from rfl, (frA h).uu']
      simp
    simp only [Matrix.mul_assoc, e3u] at mv
    set Y := row (cR σ) (incM F W.J) (incM F (fst u' hr')) * ((mat n - 1) * incM F u) with hY
    let P : Matrix (Fin j) (Fin r) (AE F E) := (1 : Matrix (Fin j) (Fin j) (AE F E)).submatrix id (Fin.castLE hr')
    have uP : incM F (fst u hr') = incM F u * P := by
      ext a k
      simp [P, Matrix.mul_apply, Matrix.one_apply, fst, incM]
    have sup : ∀ i l, ((P * Y).map C.ad) i l ≠ 0 → (i : ℕ) < r ∧ r ≤ (l : ℕ) ∧ (l : ℕ) ≤ j - 1 := fun i l hne => by
      refine ⟨by_contra fun q => hne ?_, by_contra fun q => hne ?_, by omega⟩ <;> rw [Matrix.map_apply, Matrix.mul_apply,
        Finset.sum_eq_zero, map_zero] <;> intro k _
      · rw [show P i k = 0 from Matrix.one_apply_ne fun e => q ((congrArg Fin.val e).trans_lt k.2), zero_mul]
      · have z : (mat n - 1) * incM F (fst u hr') = 0 := by rw [Matrix.sub_mul, a, Matrix.one_mul, sub_self]
        rw [show Y k l = (row (cR σ) (incM F W.J) (incM F (fst u' hr')) * ((mat n - 1) * incM F (fst u hr')) :
          Matrix (Fin r) (Fin r) (AE F E)) k ⟨l, by omega⟩ from rfl, z]
        simp
    refine ⟨Multiplicative.ofAdd fun t => ((P * Y).map C.ad) t.1.1 t.1.2, par_mem h ?_ (mid_of_move h fun z hz => ?_)⟩
    · change _ = incM F u * (1 + posM Subtype.val fun t : UnipotentBlockColumnIndex j r (j - 1) => ((P * Y).map C.ad) t.1.1 t.1.2).map C.ad.symm
      rw [posM_blk_of_support _ sup, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_map,
        show (⇑C.ad.symm ∘ ⇑C.ad) = id from funext C.ad.symm_apply_apply, Matrix.map_id, Matrix.mul_add, ← Matrix.mul_assoc, ← uP, ← mv, Matrix.sub_mul]
      simp
    · have sub : colSp (fst u hr') ≤ colSp u := Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩)
      obtain ⟨-, -, -, k⟩ := unipU_eq (σ := σ) (W := W) (colSp (fst u hr'))
      exact Submodule.span_mono (Set.image_mono sub) (((k n).1 hn).2 z fun x hx => hz x (sub hx))
  let μ := mid (cR σ) (incM F W.J) (incM F (fst u hr')) (incM F (fst u' hr'))
  have mm : ∀ s t : S, μ (mat (s * t).1) = μ (mat s.1) * μ (mat t.1) := fun s t => mid_mat h₁ (fix s) (fix t⁻¹)
  have m1 : μ (mat (1 : S).1) = 1 := (frA h₁).mid_one
  let ρ₀ : S → UA σ W.J := fun s => mkU (μ (mat s.1)) (μ (mat (s⁻¹).1)) ((frA h₁).mid_adj (adj_mat s.1))
    (by rw [← mm, mul_inv_cancel, m1]) (by rw [← mm, inv_mul_cancel, m1])
  have mem : ∀ s, ρ₀ s ∈ S := fun s => by
    have q : s.1 * (ρ₀ s)⁻¹ ∈ unipU σ W (colSp (fst u hr')) := (mem_N h₁).2 ⟨by
      rw [mat_mul, Matrix.mul_assoc]
      exact (congrArg _ ((frA h₁).mid_u _)).trans (fix s), by
      rw [mid_mat h₁ (fix s) (by rw [inv_inv]; exact (frA h₁).mid_u _)]
      exact (congrArg _ ((frA h₁).mid_mid _)).trans (mat_mul_inv (ρ₀ s))⟩
    simpa using mul_mem (inv_mem (le q)) s.2
  let ρ : S →* S := MonoidHom.mk' (fun s => ⟨ρ₀ s, mem s⟩) fun s t => Subtype.ext (mat_inj (mm s t))
  have cμ : Continuous μ := (continuous_const.add ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)).add
    continuous_const
  have c1 : Continuous fun s : S => μ (mat s.1) := cμ.comp (continuous_mat.comp continuous_subtype_val)
  have z := zero_of_retract s1 (C.good _).closed le s2 (C.lat _) ρ
    (Continuous.subtype_mk (Continuous.subtype_mk (Units.continuous_iff.2 ⟨c1, c1.comp continuous_inv⟩) _) _)
    (fun s => Subtype.ext (mat_inj ((frA h₁).mid_mid _)))
    (fun s => (mem_N h₁).trans ⟨fun q => Subtype.ext (mat_inj q.2), fun q => ⟨fix s, congrArg (fun a : S => mat a.1) q⟩⟩)
    (fun s hs => by
      obtain ⟨x, y, hx, hy⟩ := mem_ratU.1 hs
      exact mem_ratU.2 ⟨_, _, (congrArg μ hx).trans (incM_mid x).symm, (congrArg μ hy).trans (incM_mid y).symm⟩) hf.1 hf.2 h0
  have inv : ∀ b ∈ (ratV E (UnipotentBlockColumnIndex j r (j - 1))).toSubgroup, ∀ x, ct f (ι b * x) = ct f x := by
    rintro _ ⟨c, rfl⟩ x
    have := ct_rat C h H hf (blkU c) x
    rwa [ratGL_blkU] at this
  obtain ⟨c, hc⟩ := LB.isAv_ex inv
  haveI : LocallyCompactSpace S := s1.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  obtain rfl := s2.isAv_uniq (s3 f _ c hf.1 hf.2 (H.av f hf) hc) z
  exact avg_eq_of_isAv (isCoLat_ratV E _) hc x ⟨(ct_cont C H hf).comp (cι.mul continuous_const), fun γ hγ y => by
    simp only [ofAdd_add, map_mul, mul_assoc]; exact inv _ hγ _⟩

end PositivityTheory.ThKEnd.Cusp

end
