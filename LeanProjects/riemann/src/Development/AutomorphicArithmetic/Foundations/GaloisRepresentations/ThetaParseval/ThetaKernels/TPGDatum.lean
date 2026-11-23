import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcCompFinAwayPtOfNotMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GalTPDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseBadFactor
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGDecomp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseBadA

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.TP
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Bad
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc (idem)
open PositivityTheory.ThKG.Loc.Cone
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
section Supp
private def triv_pk (σ : E →ₐ[F] E) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (c : AF F) : Subgroup (UA σ J) where
  carrier := {g | c • (mat g - 1) = 0}
  one_mem' := by
    rw [Set.mem_setOf_eq, show mat (1 : UA σ J) = 1 from rfl, sub_self, smul_zero]
  mul_mem' := fun {g h} hg hh => by
    rw [Set.mem_setOf_eq] at *
    have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
      rw [show mat (g * h) = mat g * mat h from rfl]; noncomm_ring
    rw [e, smul_add, hh, add_zero, ← Matrix.smul_mul, hg, Matrix.zero_mul]
  inv_mem' := fun {g} hg => by
    rw [Set.mem_setOf_eq] at *
    have h1 : mat g⁻¹ * mat g = 1 := show mat (g⁻¹ * g) = 1 by rw [inv_mul_cancel]; rfl
    have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by rw [mul_sub, h1]; noncomm_ring
    rw [e, smul_neg, ← Matrix.mul_smul, hg, Matrix.mul_zero, neg_zero]
omit [NumberField E] in
private theorem mem_triv_pk {m : ℕ} {J : Matrix (Fin m) (Fin m) E} {c : AF F} {g : UA σ J} :
    g ∈ triv_pk σ J c ↔ c • (mat g - 1) = 0 := Iff.rfl
private theorem evI_aS_pk (S : Finset (Pl F)) : evI F (aS F S) = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [aS, Finset.sum_empty, add_zero, evI_real]
  | insert v S hv ih => rw [aS_insert hv, evI_add, evI_idem, ih, zero_add]
private theorem evFin_aS_not_pk {S : Finset (Pl F)} {v : Pl F} (h : v ∉ S) : evFin F v (aS F S) = 0 := by
  have := congrArg (evFin F v) (idem_mul_aS h)
  rwa [map_mul, evFin_idem_self, one_mul, map_zero] at this
private theorem evFin_aS_pk {S : Finset (Pl F)} {v : Pl F} (h : v ∈ S) : evFin F v (aS F S) = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact absurd h (Finset.notMem_empty v)
  | insert u S hu ih =>
    rw [aS_insert hu, map_add]
    rcases Finset.mem_insert.1 h with rfl | h'
    · rw [evFin_idem_self, evFin_aS_not_pk hu, add_zero]
    · rw [ih h', evFin_idem_ne (by rintro rfl; exact hu h'), zero_add]
variable {X : Spc F E n}
private theorem gOff_le_pk (S : Finset (Pl F)) : gOff σ X S ≤ triv_pk σ X.J (aS F S) :=
  (Subgroup.closure_le _).2 fun g hg => by
    obtain ⟨h1, h2⟩ := hg
    refine Matrix.ext fun i j => GlobalTheory.SWOpFin.tens_eq_zero_of_comp (fun v => ?_) fun w => ?_
    · rw [Matrix.smul_apply, GlobalTheory.AwayFix.Chart.compFin_smul_away]
      by_cases hv : v ∈ S
      · have := congrFun₂ (h2 v hv) i j
        rw [Matrix.map_apply] at this
        simp [this, Matrix.one_apply, apply_ite (compFin F E v)]
      · rw [evFin_aS_not_pk hv, zero_smul]
    · rw [Matrix.smul_apply, GlobalTheory.AwayFix.Chart.compInf_smul_away]
      have := congrFun₂ (h1 w) i j
      rw [Matrix.map_apply] at this
      simp [this, Matrix.one_apply, apply_ite (compInf F E w)]
private theorem gInf_le_pk (S : Finset (Pl F)) : gInf σ X ≤ triv_pk σ X.J (1 - aS F S) :=
  (Subgroup.closure_le _).2 fun _ hg => hg _ (by rw [evI_sub, evI_one, evI_aS_pk, sub_self])
private theorem loc_le_pk {S : Finset (Pl F)} {v : Pl F} (h : v ∈ S) : locGrp σ X v ≤ triv_pk σ X.J (1 - aS F S) :=
  (Subgroup.closure_le _).2 fun _ hg => hg _ (by rw [map_sub, map_one, evFin_aS_pk h, sub_self])
end Supp
section Cut
variable {Y : Spc F E n}
private theorem comm_of_pk {ι : Type} [Fintype ι] [DecidableEq ι] {c : AF F} {A B : Matrix ι ι (AE F E)} (h1 : c • (A - 1) = A - 1)
    (h2 : c • (B - 1) = 0) : A * B = B * A := by
  have a1 : (A - 1) * (B - 1) = 0 := by rw [← h1, Matrix.smul_mul, ← Matrix.mul_smul, h2, Matrix.mul_zero]
  have a2 : (B - 1) * (A - 1) = 0 := by rw [← h1, Matrix.mul_smul, ← Matrix.smul_mul, h2, Matrix.zero_mul]
  have : A * B - B * A = (A - 1) * (B - 1) - (B - 1) * (A - 1) := by noncomm_ring
  exact sub_eq_zero.1 (by rw [this, a1, a2, sub_zero])
private def cutG_pk (c : AF F) (hc : c * c = c) : G2 σ Y →* G2 σ Y :=
  MonoidHom.mk' (fun g => ⟨⟨Euler.cut c (mat2 g), Euler.cut c (mat2 g⁻¹),
    by rw [Euler.cut_mul hc, show mat2 g * mat2 g⁻¹ = 1 from g.1.mul_inv]; exact Euler.cut_one,
    by rw [Euler.cut_mul hc, show mat2 g⁻¹ * mat2 g = 1 from g.1.inv_mul]; exact Euler.cut_one⟩,
    Euler.cut_form hc _ g.2⟩) fun _ _ => Subtype.ext (Units.ext (Euler.cut_mul hc _ _).symm)
omit [NumberField E] in
private theorem idempotentCut_mem_stabilizer {c : AF F} (hc : c * c = c) (g : G2 σ Y) : mat2 (cutG_pk c hc g) = Euler.cut c (mat2 g) := rfl
private theorem cutG_mem_pk {B : Base F E} {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K) {c : AF F} (hc : c * c = c)
    (i1 : ∀ u, evFin F u c ∈ u.adicCompletionIntegers F) (i2 : ∀ u, evFin F u (1 - c) ∈ u.adicCompletionIntegers F) {k : G2 σ Y}
    (hk : k ∈ K) : cutG_pk c hc k ∈ K := by
  refine (hK _).2 ⟨fun w => ?_, fun z z' hz hz' k' hk' => ?_⟩
  · have e : (mat2 (cutG_pk c hc k)).map (piInf (B.emb w)) = piInf (B.emb w) (algebraMap _ _ (1 - c)) • 1 +
        piInf (B.emb w) (algebraMap _ _ c) • (mat2 k).map (piInf (B.emb w)) := by
      ext i j
      rw [Matrix.map_apply, idempotentCut_mem_stabilizer, Euler.cut, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
        Matrix.smul_apply, Matrix.smul_apply, map_add, Algebra.smul_def (1 - c), Algebra.smul_def c, map_mul, map_mul, Matrix.map_apply,
        Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [e]
    exact ((Commute.one_left _).smul_left _).add_left ((((hK k).1 hk).1 w).smul_left _)
  · obtain ⟨k₁, rfl, h3⟩ : ∃ k₁, k' = cutG_pk c hc k₁ ∧ k₁ ∈ ({k, k⁻¹} : Set (G2 σ Y)) := by
      rcases hk' with rfl | rfl
      exacts [⟨k, rfl, .inl rfl⟩, ⟨k⁻¹, (map_inv _ k).symm, .inr rfl⟩]
    obtain ⟨b1, b2⟩ := ((hK k).1 hk).2 z z' hz hz' k₁ h3
    rw [idempotentCut_mem_stabilizer, Euler.cut, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact ⟨add_mem (latHat_smul i2 hz) (latHat_smul i1 b1), add_mem (latHat_smul i2 hz') (latHat_smul i1 b2)⟩
private theorem cut_iwa_pk {B : Base F E} {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K) {a : G2 σ Y → ℝ} (ha : IsHgt K a) {c : AF F}
    (hc : c * c = c) (i1 : ∀ u, evFin F u c ∈ u.adicCompletionIntegers F) (i2 : ∀ u, evFin F u (1 - c) ∈ u.adicCompletionIntegers F)
    {x : G2 σ Y} (hx : c • (mat2 x - 1) = mat2 x - 1) :
    ∃ p t k, IsPar p t ∧ k ∈ K ∧ c • (mat2 k - 1) = mat2 k - 1 ∧ x = p * k := by
  obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa x
  refine ⟨cutG_pk c hc p, ⟨Euler.cut c t.1, Euler.cut c (t⁻¹).1, by rw [Euler.cut_mul hc, t.mul_inv]; exact Euler.cut_one,
    by rw [Euler.cut_mul hc, t.inv_mul]; exact Euler.cut_one⟩, cutG_pk c hc k, ?_, cutG_mem_pk hK hc i1 i2 hk, ?_, ?_⟩
  · rw [isPar_iff] at hp ⊢
    change Euler.cut c (mat2 p) * _ = _ * Euler.cut c t.1
    rw [Euler.cut, Euler.cut, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, hp,
      Matrix.one_mul, Matrix.mul_one]
  · rw [idempotentCut_mem_stabilizer, Euler.cut_sub, smul_smul, hc]
  · rw [← map_mul]
    exact Subtype.ext (Units.ext (Euler.cut_eq.2 hx).symm)
end Cut
section Fix
variable {Y : Spc F E n}
private theorem cut_add_pk {S R k : Type} [CommRing S] [CommRing R] [Algebra S R] [Fintype k] [DecidableEq k] {c₁ c₂ : S} (h : c₁ * c₂ = 0)
    (A : Matrix k k R) : Euler.cut (c₁ + c₂) A = Euler.cut c₁ A * Euler.cut c₂ A := by
  have e : ∀ c : S, Euler.cut c A = 1 + c • (A - 1) := fun c => eq_add_of_sub_eq' (Euler.cut_sub A)
  have h' : c₂ * c₁ = 0 := by rw [mul_comm, h]
  rw [e, e, e]
  simp only [add_mul, mul_add, one_mul, mul_one, add_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, h', zero_smul, add_zero]
  abel
private theorem int_aS_pk (T : Finset (Pl F)) (u : Pl F) : evFin F u (aS F T) ∈ u.adicCompletionIntegers F := by
  by_cases h : u ∈ T
  · rw [evFin_aS_pk h]; exact one_mem _
  · rw [evFin_aS_not_pk h]; exact zero_mem _
private theorem tendsto_cutG_pk [DecidableEq (Pl F)] (S : Finset (Pl F)) (k : G2 σ Y) :
    Tendsto (fun T : Finset (Pl F) => cutG_pk (aS F (S ∪ T)) (aS_mul_self _) k) atTop (𝓝 k) := by
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  have t0 : Tendsto (fun T : Finset (Pl F) => aS F (S ∪ T)) atTop (𝓝 1) :=
    tendsto_aS.comp (tendsto_atTop_mono (fun T => Finset.subset_union_right) tendsto_id)
  have t1 : ∀ A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E),
      Tendsto (fun T : Finset (Pl F) => Euler.cut (aS F (S ∪ T)) A) atTop (𝓝 A) := fun A => by
    have c : Continuous fun x : AF F => Euler.cut x A := by
      unfold Euler.cut
      refine continuous_matrix fun i j => ?_
      simp only [Matrix.add_apply, Matrix.smul_apply]
      fun_prop
    have := (c.tendsto 1).comp t0
    rwa [show Euler.cut (1 : AF F) A = A by simp [Euler.cut]] at this
  refine tendsto_subtype_rng.2 (Units.isEmbedding_embedProduct.tendsto_nhds_iff.2 ?_)
  exact (t1 (mat2 k)).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (t1 (mat2 k⁻¹)))
private theorem fix_off_pk {B : Base F E} {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K) {I : Type} (om₂ : G2 σ Y →* Module.End ℂ (I → ℂ))
    {Ψ : I → ℂ} (hc : ∀ x, Continuous fun g => om₂ g Ψ x) {S : Finset (Pl F)}
    (hl : ∀ v ∉ S, ∀ k ∈ K, At (evFin F v) (mat2 k - 1) → om₂ k Ψ = Ψ) {k : G2 σ Y} (hk : k ∈ K)
    (h : aS F S • (mat2 k - 1) = 0) : om₂ k Ψ = Ψ := by
  classical
  have step : ∀ T : Finset (Pl F), om₂ (cutG_pk (aS F (S ∪ T)) (aS_mul_self _) k) Ψ = Ψ := fun T => by
    induction T using Finset.induction_on with
    | empty =>
      have : cutG_pk (aS F (S ∪ ∅)) (aS_mul_self _) k = 1 :=
        Subtype.ext (Units.ext (sub_eq_zero.1 (Euler.cut_sub _ |>.trans (by rw [Finset.union_empty]; exact h))))
      rw [this, map_one]; rfl
    | insert v T hv ih =>
      by_cases hm : v ∈ S ∪ T
      · simpa only [Finset.union_insert, Finset.insert_eq_self.2 hm] using ih
      have e : cutG_pk (aS F (S ∪ insert v T)) (aS_mul_self _) k =
          cutG_pk (idem F v) (idem_mul_self v) k * cutG_pk (aS F (S ∪ T)) (aS_mul_self _) k := by
        refine Subtype.ext (Units.ext ?_)
        change Euler.cut (aS F (S ∪ insert v T)) (mat2 k) = Euler.cut (idem F v) (mat2 k) * Euler.cut (aS F (S ∪ T)) (mat2 k)
        rw [Finset.union_insert, aS_insert hm, cut_add_pk (idem_mul_aS hm)]
      have hvS : v ∉ S := fun h' => hm (Finset.mem_union_left _ h')
      have i2 : ∀ u, evFin F u (1 - idem F v) ∈ u.adicCompletionIntegers F := fun u => by
        rw [map_sub, map_one]; exact sub_mem (one_mem _) (idem_int v u)
      rw [e, map_mul, Module.End.mul_apply, ih, hl v hvS _ (cutG_mem_pk hK _ (idem_int v) i2 hk)]
      rw [idempotentCut_mem_stabilizer, Euler.cut_sub]
      exact at_idem v _
  refine funext fun x => tendsto_nhds_unique (((hc x).tendsto k).comp (tendsto_cutG_pk S k)) (tendsto_const_nhds.congr fun T => ?_)
  exact (congrFun (step T) x).symm
end Fix
section Main
variable {X : Spc F E n}
private theorem triv_idem_pk {S : Finset (Pl F)} {v : Pl F} (h : v ∈ S) : triv_pk σ X.J (aS F S) ≤ triv_pk σ X.J (idem F v) := fun g hg => by
  have e : idem F v = idem F v * aS F S := af_ext' (by rw [evI_mul, evI_idem, zero_mul]) fun u => by
    rw [map_mul]
    by_cases hu : u = v
    · rw [hu, evFin_aS_pk h, mul_one]
    · rw [evFin_idem_ne hu, zero_mul]
  rw [mem_triv_pk, e, mul_smul, mem_triv_pk.1 hg, smul_zero]
private theorem off_triv_pk {v : Pl F} {g : UA σ X.J} (h : OffAt v g) : g ∈ triv_pk σ X.J (idem F v) :=
  Matrix.ext fun i j => idem_off (by
    have := congrFun₂ h i j
    rw [Matrix.map_apply] at this
    simp [this, Matrix.one_apply, apply_ite (compFin F E v)])
private theorem triv_mul_pk {v : Pl F} {y : UA σ X.J} (hy : y ∈ triv_pk σ X.J (idem F v)) {u : Matrix (Fin n) (Fin d) (AE F E)}
    (hu : At (evFin F v) u) : mat y * u = u := by
  have : (mat y - 1) * u = 0 := by rw [← idem_smul hu, Matrix.mul_smul, ← Matrix.smul_mul, mem_triv_pk.1 hy, Matrix.zero_mul]
  rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
private theorem triv_emb_pk {e : UA σ X.J × UA σ X.J →* G2 σ X} (he : ∀ g g', IsEmb g g' (e (g, g'))) {c : AF F} {g : UA σ X.J}
    (h : g ∈ triv_pk σ X.J c) : c • (mat2 (e (g, 1)) - 1) = 0 := by
  rw [he g 1, show mat (1 : UA σ X.J) = 1 from rfl, ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg,
    Matrix.fromBlocks_add, Matrix.fromBlocks_smul, ← sub_eq_add_neg, mem_triv_pk.1 h]
  simp
private theorem one_sub_smul'_pk {ι : Type} {A : Matrix ι ι (AE F E)} [DecidableEq ι] {c : AF F} (h : c • (A - 1) = 0) :
    (1 - c) • (A - 1) = A - 1 := by rw [sub_smul, one_smul, h, sub_zero]
private def stabG_pk {W : Spc F E d} (om : Rep σ X W) (Φ : Fn F n d) : Subgroup (UA σ X.J) where
  carrier := {g | om (g, 1) Φ = Φ}
  one_mem' := by
    rw [Set.mem_setOf_eq, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one]; rfl
  mul_mem' := fun {g h} hg hh => by
    rw [Set.mem_setOf_eq] at *
    rw [show ((g * h, 1) : UA σ X.J × UA σ W.J) = (g, 1) * (h, 1) by simp, map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' := fun {g} hg => by
    rw [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hg]
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl,
      map_one]
    rfl
theorem datum_k : _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.Datum_k := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om P hn K a e hK ha he ν hν S uW H φ hfin hbump hoff f₀ hf₀ n0
  classical
  have h0 : min n 0 = 0 := Nat.min_zero n
  obtain ⟨dd, om₂, S₂, l, d1, d2, d3, d4⟩ := T.dbl F E σ B n d X W M χX χW om n 0 d 0 P
  obtain ⟨c₀, c0, hc⟩ := d4 ν hν
  have c1 := Complex.ofReal_ne_zero.2 c0.ne'
  have hSB := hfin.1
  have hs := (hfin.2.and P.good.std).mono fun v h => h.1.trans h.2
  have hne : ∀ v, φ v ≠ 0 := fun v => by
    by_cases h : v ∈ S
    exacts [(hbump v h).2.1, hoff v h ▸ (P.good.vac v).2.1]
  have m := GlobalTheory.TensUniq.pure_mem_schA f₀ φ hSB hs
  have m0 := GlobalTheory.EvNonzero.pure_ne_zero f₀ n0 φ hne hs
  have fx : ∀ v ∉ S, ∀ k ∈ K, At (evFin F v) (mat2 k - 1) → om₂ k (boxFun (pure f₀ φ) (star (pure f₀ φ))) = _ := fun v h k hk h' =>
    fix_box hSB hs (hoff v h ▸ T.vacFix F E σ B n d X W M n 0 d 0 P.base P.herm P.skew P.good χW P.hW dd om₂ d3 d1.weil K hK v
      (fun w hw => uW w (by show ¬ w.under (𝓞 F) ∈ (S : Set (Pl F)); rw [hw]; exact h)) k hk h')
  have e1 := fun v R (c : ℂ) (h' : Acts (evFin F v) R (φ v) (c • φ v)) => eig (f := f₀) hSB hs h'
  generalize pure f₀ φ = Φ at *
  have hbox := (d2 Φ m Φ m).1
  have bx : ∀ g, om₂ (e (g, 1)) (boxFun Φ (star Φ)) = boxFun (om (g, 1) Φ) (star Φ) := fun g => by
    simpa [detInv, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl] using ((d2 Φ m Φ m).2 1 g 1 _ (he g 1)).2
  have cf : ∀ g, l (om₂ (e (g, 1)) (boxFun Φ (star Φ))) = c₀ * coef om ν Φ g := fun g => by
    rw [bx, hc _ (P.weil.isUSplitting.pres _ _ m) _ m]; rfl
  have L := _root_.GlobalTheory.ThK.Dbl.Bad.law_k P.base d1 hbox
  have fk : ∀ k ∈ K, aS F S • (mat2 k - 1) = 0 → om₂ k (boxFun Φ (star Φ)) = boxFun Φ (star Φ) := fun k hk h =>
    fix_off_pk hK om₂ (fun x => d1.weil.2.1.cont _ (ev_adm x) _ hbox) fx hk h
  have key : ∀ c ∈ gOff σ X S, ∀ p t k, IsPar p t → k ∈ K → aS F S • (mat2 k - 1) = 0 → e (c, 1) = p * k →
      ∀ y ∈ triv_pk σ X.J (1 - aS F S), coef om ν Φ (y * c) = (χW (Matrix.GeneralLinearGroup.det t) : ℂ) *
        ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ ((d : ℂ) / 2) * coef om ν Φ y := fun c hc' p t k hp hk hk0 hx y hy => by
    have cm : y * c = c * y := Subtype.ext (Units.ext (comm_of_pk (one_sub_smul'_pk (mem_triv_pk.1 (gOff_le_pk S hc'))) (mem_triv_pk.1 hy)).symm)
    have ck : k * e (y, 1) = e (y, 1) * k := Subtype.ext (Units.ext (comm_of_pk (one_sub_smul'_pk hk0) (triv_emb_pk he hy)))
    have e2 : e (y * c, 1) = p * (e (y, 1) * k) := by
      rw [cm, show ((c * y, 1) : UA σ X.J × UA σ X.J) = (c, 1) * (y, 1) by simp, map_mul, hx, mul_assoc, ck]
    refine mul_left_cancel₀ c1 ?_
    rw [mul_left_comm, ← cf, ← cf, e2]
    have := L p t (e (y, 1) * k) hp
    beta_reduce at this
    rw [this, map_mul, Module.End.mul_apply, fk k hk hk0]
  have st : ⨆ v ∈ S, H v ≤ stabG_pk om Φ :=
    iSup₂_le fun v hv g hg => (e1 v _ 1 (by rw [one_smul]; exact (hbump v hv).2.2.2.2.2.1 g hg)).trans (one_smul _ _)
  have hL : ∀ v ∈ S, H v ≤ locGrp σ X v := fun v hv => (hbump v hv).2.2.1
  have hH : ⨆ v ∈ S, H v ≤ triv_pk σ X.J (1 - aS F S) := iSup₂_le fun v hv => (hL v hv).trans (loc_le_pk hv)
  refine ⟨?_, fun x hx b hb c hc' => ⟨fun hbn => ?_, ?_⟩⟩
  · rw [coef, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one]; exact sq_ne ν hν m m0
  · obtain ⟨-, -, -, -, -, -, -, hdec, -⟩ := _root_.UpperTheory.TP.decomp_k T F E σ B n X P.base P.herm S
    obtain ⟨q, q1, q2, q3⟩ := hdec b hb
    obtain ⟨v, hv, hq⟩ : ∃ v ∈ S, q v ∉ ⨆ v ∈ S, H v := by
      by_contra hh
      push Not at hh
      exact hbn (q3 _ hh)
    obtain ⟨u, z, z', hu, hz, r1, r2⟩ := (hbump v hv).2.2.2.2.2.2 (q v) (q1 v)
      fun h => hq (Subgroup.mem_iSup_of_mem v (Subgroup.mem_iSup_of_mem hv h))
    have hm : mat (x * b * c) * u = mat (q v) * u := by
      have a1 : At (evFin F v) (mat (q v) * u) := fun t ht => by rw [← Matrix.mul_smul, hu t ht, Matrix.mul_zero]
      have a2 : gInf σ X ≤ triv_pk σ X.J (idem F v) := (Subgroup.closure_le _).2 fun _ hg => hg _ (evI_idem v)
      have a3 := triv_mul_pk (off_triv_pk (q2 v hv)) hu
      have a4 := triv_mul_pk (triv_idem_pk hv (gOff_le_pk S hc')) hu
      have a5 : mat (x * b * c) = mat x * mat (q v) * mat ((q v)⁻¹ * b) * mat c := by
        rw [show x * b * c = x * q v * ((q v)⁻¹ * b) * c by group]; rfl
      rw [a5, Matrix.mul_assoc, a4, Matrix.mul_assoc, a3, Matrix.mul_assoc, triv_mul_pk (a2 hx) a1]
    exact _root_.GlobalTheory.ThK.Dbl.Bad.orth_k P hν m m0 hz (e1 v _ _ r1) (e1 v _ _ (by rwa [hm]))
  · have i1 : ∀ u, evFin F u (1 - aS F S) ∈ u.adicCompletionIntegers F := fun u => by
      rw [map_sub, map_one]; exact sub_mem (one_mem _) (int_aS_pk S u)
    have i2 : ∀ u, evFin F u (1 - (1 - aS F S)) ∈ u.adicCompletionIntegers F := fun u => by
      rw [sub_sub_cancel]; exact int_aS_pk S u
    have hc0 := triv_emb_pk he (gOff_le_pk S hc')
    obtain ⟨p, t, k, hp, hk, hk0, hx', ht⟩ : ∃ p t k, IsPar p t ∧ k ∈ K ∧ aS F S • (mat2 k - 1) = 0 ∧ e (c, 1) = p * k ∧
        (IntAll c → t = 1) := by
      by_cases hI : IntAll c
      · exact ⟨1, 1, e (c, 1), par_one, _root_.GlobalTheory.ThK.Dbl.Bad.emb_mem_k P.base P.herm h0 hK he hI, hc0, (one_mul _).symm, fun _ => rfl⟩
      · have hid : (1 - aS F S) * (1 - aS F S) = 1 - aS F S := by
          linear_combination aS_mul_self S
        obtain ⟨p, t, k, hp, hk, hk0, hx'⟩ := cut_iwa_pk hK ha hid i1 i2 (one_sub_smul'_pk hc0)
        refine ⟨p, t, k, hp, hk, ?_, hx', fun h => absurd h hI⟩
        rwa [sub_smul, one_smul, sub_eq_self] at hk0
    refine ⟨(χW (Matrix.GeneralLinearGroup.det t) : ℂ) * ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ ((d : ℂ) / 2), ?_,
      fun h => ?_, fun x' hx'' b' hb' => ?_⟩
    · rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (absE_pos _), hx', ha.val p t hp k hk]
      simp
    · simp [ht h]
    · have hy : x' * b' ∈ triv_pk σ X.J (1 - aS F S) := mul_mem (gInf_le_pk S hx'') (hH hb')
      have hf : om (b', 1) Φ = Φ := st hb'
      rw [key c hc' p t k hp hk hk0 hx' _ hy, coef, coef,
        show ((x' * b', 1) : UA σ X.J × UA σ W.J) = (x', 1) * (b', 1) by simp, map_mul, Module.End.mul_apply, hf]
end Main
end UpperTheory.TP
end
end
