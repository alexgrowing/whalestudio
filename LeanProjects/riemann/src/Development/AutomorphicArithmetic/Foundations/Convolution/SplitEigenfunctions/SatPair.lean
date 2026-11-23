import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDualC
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SatOfPol

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

section General

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ G V} {ρ : Representation ℂ G W} {K : Subgroup G} {h : G → ℂ} {x : V} {y : W}

private theorem pair_heckeVec (hK : IsCommensurated K) (hh : h ∈ Hecke ℂ K) (hx : x ∈ fixed σ K)
    (hy : y ∈ fixed ρ K) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (θ : G ≃* G) (hθ : ∀ k, k ∈ K ↔ θ k ∈ K)
    (hi : ∀ g v w, β (σ (θ g) v) (ρ g w) = β v w)
    (ht : ∀ g, h g ≠ 0 → ∃ a ∈ K, ∃ b ∈ K, ∃ t, θ t⁻¹ = t ∧ g = a * t * b) :
    β (heckeVec σ K h x) y = β x (heckeVec ρ K h y) := by
  have hf := GlobalTheory.LGrp.mem_fixed.1 hx
  have hg := GlobalTheory.LGrp.mem_fixed.1 hy
  have bi : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β (σ (a * t * b) x) y = β (σ t x) y := fun a ha b hb t => by
    obtain ⟨a, rfl⟩ := θ.surjective a
    rw [map_mul σ, map_mul σ, Module.End.mul_apply, Module.End.mul_apply, hf b hb]
    exact (congrArg (β _) (hg a ((hθ a).2 ha)).symm).trans (hi a _ _)
  have bi' : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β x (ρ (a * t * b) y) = β x (ρ t y) := fun a ha b hb t => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg b hb]
    exact (congrArg (fun u => β u _) (hf _ ((hθ a).1 ha)).symm).trans (hi a _ _)
  have inv : ∀ t, β (σ (θ t⁻¹) x) y = β x (ρ t y) := fun t => by
    rw [← hi t⁻¹ x (ρ t y)]; simp
  have e1 := (β.flip y).toAddMonoidHom.map_finsum (finite_heckeVec hK hh σ x)
  have e2 := (β x).toAddMonoidHom.map_finsum (finite_heckeVec hK hh ρ y)
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  change β (h c.out • σ c.out x) y = β x (h c.out • ρ c.out y)
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases h0 : h c.out = 0
  · simp [h0]
  obtain ⟨a, ha, b, hb, t, htt, e⟩ := ht _ h0
  congr 1
  rw [e, bi _ ha _ hb, bi' _ ha _ hb, ← inv, htt]

private theorem exists_fixed_pair [TopologicalSpace G] [IsTopologicalGroup G] (hρ : IsSmooth ρ)
    (hK : IsCompact (K : Set G)) (l : W →ₗ[ℂ] ℂ) (hl : ∀ k ∈ K, ∀ v, l (ρ k v) = l v) (y : W) :
    ∃ y' ∈ fixed ρ K, l y' = l y := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hfi : (GlobalTheory.OrbitAvg.stab ρ K y).FiniteIndex := by
    have ho : IsOpen (GlobalTheory.OrbitAvg.stab ρ K y : Set K) := (hρ y).preimage continuous_subtype_val
    haveI := (GlobalTheory.OrbitAvg.stab ρ K y).quotient_finite_of_isOpen ho
    exact Subgroup.finiteIndex_of_finite_quotient
  refine ⟨GlobalTheory.OrbitAvg.avg ρ K y,
    GlobalTheory.LGrp.mem_fixed.2 fun u hu => GlobalTheory.OrbitAvg.avg_invariant ρ K hfi ⟨u, hu⟩, ?_⟩
  haveI := Fintype.ofFinite (K ⧸ GlobalTheory.OrbitAvg.stab ρ K y)
  have hc : ((GlobalTheory.OrbitAvg.stab ρ K y).index : ℂ) ≠ 0 := by exact_mod_cast hfi.index_ne_zero
  have h1 : ∀ q : K ⧸ GlobalTheory.OrbitAvg.stab ρ K y, l (ρ (q.out : K) y) = l y := fun q => hl _ q.out.2 y
  simp only [GlobalTheory.OrbitAvg.avg, GlobalTheory.OrbitAvg.avgH, GlobalTheory.OrbitAvg.cv, finsum_eq_sum_of_fintype, map_smul, map_sum]
  rw [Finset.sum_congr rfl fun q _ => h1 q, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Subgroup.index, nsmul_eq_mul, smul_eq_mul, inv_mul_cancel_left₀ hc]

end General

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.ConjPlace in

private theorem sat_eq_of_eig {E : Type} [Field E] [NumberField E] {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (hσ : IsSmooth σ) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (hi : ∀ g x y, β (σ (GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) n g) x) (ρ g y) = β x y)
    {Y : W} {C C' : Multiset ℂˣ} (hY : IsSatVecGL w ρ Y C') {x₀ : V} (hx₀ : β x₀ Y ≠ 0)
    (hE : ∀ x ∈ fixed σ (KGL w n), C.card = n ∧ ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n,
      β (heckeVec σ (KGL w n) (Tj ℂ n (Ov E w) ϖ j) x) Y = satEig (qV E w) n C j * β x Y) : C = C' := by
  classical
  have hKc : IsCompact (KGL w n : Set (GL (Fin n) (w.adicCompletion E))) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w)
  let c := RingEquiv.refl (w.adicCompletion E)
  have hc : ∀ a, Valued.v (c a) = Valued.v a := fun _ => rfl
  have hK := mem_iff_invT (n := n) c (map_mem_Ov_iff c hc)
  have hfY := GlobalTheory.LGrp.mem_fixed.1 hY.2.1
  obtain ⟨x, hxK, hx⟩ := exists_fixed_pair hσ hKc (β.flip Y) (fun k hk v => by
    obtain ⟨k', rfl⟩ := (GlobalTheory.LFun.ConjPlace.invT c n).surjective k
    have := hi k' v Y
    rwa [hfY _ ((hK k').2 hk)] at this) x₀
  have hne : β x Y ≠ 0 := fun h0 => hx₀ (hx.symm.trans h0)
  obtain ⟨p, hp⟩ := exists_isUnifV w
  obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p :=
    ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
  obtain ⟨hcard, hE'⟩ := hE x hxK
  refine eq_of_satEig_eq (qV_ne_zero w) hcard hY.2.2.1 fun j hj => ?_
  have key := pair_heckeVec (Final.GLintComm E w n) (Tj_mem_hecke hp j) hxK hY.2.1 β
    (GlobalTheory.LFun.ConjPlace.invT c n) hK hi
    (fun g hg => by
      rw [Tj_apply] at hg
      obtain ⟨a, ha, b, hb, e⟩ : ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
          g = a * dGL n ϖ j * b := by
        by_contra hn
        exact hg (if_neg hn)
      exact ⟨a, ha, b, hb, _, invT_dGL c ϖ j, e⟩)
  rw [hE' _ hp j hj, hY.2.2.2 _ hp j hj, map_smul, smul_eq_mul] at key
  exact mul_right_cancel₀ hne key

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.satPair :
    SatPair := by
  intro E _ _ _ V Q B hB hne w T hsm heq hker C C' hC hQ
  classical
  let σ : Representation ℂ (GL (Fin 2) (Kv w)) V :=
    (GlobalTheory.PRep.sub (finRep E 2) V fun k => hB.st (.fin k)).comp (locGL E 2 w)
  have hsmooth : GlobalTheory.PRep.IsSmooth σ := by
    intro x
    let S : Subgroup (GL (Fin 2) (Kv w)) :=
      { carrier := {g | σ g x = x}
        mul_mem' := fun {a b} ha hb => by
          change σ (a * b) x = x
          rw [map_mul, Module.End.mul_apply, show σ b x = x from hb]; exact ha
        one_mem' := by change σ 1 x = x; rw [map_one]; rfl
        inv_mem' := fun {a} ha => by
          change σ a⁻¹ x = x
          conv_lhs => rw [← show σ a x = x from ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
    refine Subgroup.isOpen_of_mem_nhds S (g := 1) ?_
    filter_upwards [hsm x] with y hy
    exact Subtype.ext (Subtype.ext (funext fun g => hy g))
  have hker0 : ∀ y : Q.V, (∀ x, B x y = 0) → y = 0 := by
    have hst : IsStable ((LinearMap.ker B.flip).map Q.V.subtype) := by
      rintro o _ ⟨y, hy, rfl⟩
      have hy' : ∀ x, B x y = 0 := fun x => LinearMap.congr_fun (LinearMap.mem_ker.1 hy) x
      refine ⟨Q.op o y, LinearMap.mem_ker.2 (LinearMap.ext fun x => ?_), rfl⟩
      change B x (Q.op o y) = 0
      cases o with
      | fin k =>
        let x' : V := ⟨act (.fin k⁻¹) x.1, hB.st _ _ x.2⟩
        have e : (⟨act (.fin k) x'.1, hB.st _ _ x'.2⟩ : V) = x := Subtype.ext (by
          change finRep E 2 k (finRep E 2 k⁻¹ x.1) = x.1
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl)
        exact (congrArg (fun u => B u (Q.op (.fin k) y)) e).symm.trans ((hB.fin k x' y).trans (hy' x'))
      | cpt k =>
        let x' : V := ⟨act (.cpt k⁻¹) x.1, hB.st _ _ x.2⟩
        have e : (⟨act (.cpt k) x'.1, hB.st _ _ x'.2⟩ : V) = x := Subtype.ext (by
          change cptRep E 2 k (cptRep E 2 k⁻¹ x.1) = x.1
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl)
        exact (congrArg (fun u => B u (Q.op (.cpt k) y)) e).symm.trans ((hB.cpt k x' y).trans (hy' x'))
      | lie X =>
        have h := hB.lie X x y
        rw [hy' _, zero_add] at h
        exact h
    intro y hy
    rcases Q.irred _ (Submodule.map_subtype_le _ _) hst with h | h
    · have hm : y.1 ∈ (LinearMap.ker B.flip).map Q.V.subtype :=
        ⟨y, LinearMap.mem_ker.2 (LinearMap.ext hy), rfl⟩
      rw [h] at hm
      exact Subtype.ext ((Submodule.mem_bot _).1 hm)
    · exfalso
      refine hne (LinearMap.ext fun x => LinearMap.ext fun z => ?_)
      have hz : z.1 ∈ (LinearMap.ker B.flip).map Q.V.subtype := by rw [h]; exact z.2
      obtain ⟨u, hu, e⟩ := hz
      have e' : u = z := Subtype.ext e
      subst e'
      exact LinearMap.congr_fun (LinearMap.mem_ker.1 hu) x
  have hD := TC.hasSatGL_dual ((CG.hasSat_mk Q w C').1 hQ)
  obtain ⟨Y, hY⟩ := hD.exists_vec
  let β : V →ₗ[ℂ] (TC.dual Q).V →ₗ[ℂ] ℂ := B.compl₂ (TC.toDual Q).symm.toLinearMap
  have hβ : ∀ x y, β x (TC.toDual Q y) = B x y := fun x y => by simp [β]
  have hβ' : ∀ x, β x Y = B x ((TC.toDual Q).symm Y) := fun _ => rfl
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, β x₀ Y ≠ 0 := by
    by_contra hn
    push_neg at hn
    refine hY.1 ?_
    have h0 := hker0 ((TC.toDual Q).symm Y) hn
    simpa using h0
  have hi : ∀ g x y, β (σ (GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) 2 g) x) ((TC.dual Q).locRep w g y) = β x y := by
    intro g x y
    obtain ⟨y, rfl⟩ := (TC.toDual Q).surjective y
    rw [TC.locRep_toDual, hβ, hβ]
    have e := hB.fin (locGL E 2 w (GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) 2 g)) x y
    refine Eq.trans ?_ e
    refine congrArg (B _) ?_
    rw [CuspSub.locRep_eq]
    refine Subtype.ext ?_
    change act (.fin _) y.1 = act (.fin _) y.1
    refine congrArg (fun k => act (.fin (locGL E 2 w k)) y.1) (Units.ext (Matrix.ext fun i j => ?_))
    rw [GlobalTheory.LFun.ConjPlace.invT_val]
    rfl
  have hfin := sat_eq_of_eig (n := 2) hsmooth β hi hY hx₀ (fun x hx => by
    have hfix : Fix w x.1.1 := fun g k hk => congrArg (fun u : V => u.1.1 g) (GlobalTheory.LGrp.mem_fixed.1 hx k hk)
    refine ⟨(hC x hfix 1).card, fun ϖ hϖ j hj => ?_⟩
    have hTz : ∀ g, T (GlobalTheory.LFun.heckeVec σ (GlobalTheory.LFun.KGL w 2) (Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j) x) g =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) 2 C j * T x g := by
      intro g
      let L : V →+ ℂ := (Pi.evalAddMonoidHom _ g).comp T.toAddMonoidHom
      have e1 := L.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w 2) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) σ x)
      have e2 := (hC x hfix g).eig ϖ hϖ j hj 1
      refine e1.trans (Eq.trans (finsum_congr fun c => ?_) (e2.trans ?_))
      · change T (Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out • σ c.out x) g = _
        rw [map_smul, Pi.smul_apply, smul_eq_mul, heq x (σ c.out x) c.out (fun _ => rfl) g, one_mul]
        rfl
      · simp
    have hz : T (GlobalTheory.LFun.heckeVec σ (GlobalTheory.LFun.KGL w 2) (Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j) x -
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) 2 C j • x) = 0 := by
      funext g
      simp [map_sub, hTz]
    have h2 := LinearMap.congr_fun (hker _ hz) ((TC.toDual Q).symm Y)
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.zero_apply, sub_eq_zero, smul_eq_mul] at h2
    exact h2)
  rw [hfin, Multiset.map_map]
  simp
