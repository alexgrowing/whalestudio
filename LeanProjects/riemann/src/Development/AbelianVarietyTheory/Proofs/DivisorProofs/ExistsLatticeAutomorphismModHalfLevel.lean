import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UniformLevelMultiplicity
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLiftConditions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalVectorMemIdealCompletedLatticeIffStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelSubgroup
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabInduce

section Abstract

variable {R L A : Type} [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup A]

theorem exists_induced (N : Submodule R L) (φ : L →+ A) (s : R → A →+ A) (H C : AddSubgroup A)
    (hφs : ∀ r a, φ (r • a) = s r (φ a)) (hs : ∀ r, ∀ z ∈ C, s r z ∈ C) (hφ : ∀ a, φ a ∈ H)
    (hN : ∀ a, φ a ∈ C ↔ a ∈ N) (hon : ∀ z ∈ H, ∃ a, z - φ a ∈ C)
    (k : A →+ A) (hks : ∀ r z, k (s r z) = s r (k z)) (hkH : ∀ z ∈ H, k z ∈ H) (hkC : ∀ z ∈ C, k z ∈ C) :
    ∃ f : (L ⧸ N) →ₗ[R] (L ⧸ N), ∀ a b, f (N.mkQ a) = N.mkQ b ↔ k (φ a) - φ b ∈ C := by
  choose g hg using fun a => hon (k (φ a)) (hkH _ (hφ a))
  have key : ∀ a b, N.mkQ (g a) = N.mkQ b ↔ k (φ a) - φ b ∈ C := by
    intro a b
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hN, map_sub]
    constructor
    · intro h
      have := add_mem (hg a) h
      rwa [sub_add_sub_cancel] at this
    · intro h
      have := sub_mem h (hg a)
      rwa [sub_sub_sub_cancel_left] at this
  let g0 : L →ₗ[R] (L ⧸ N) :=
    { toFun := fun a => N.mkQ (g a)
      map_add' := fun a b => by
        rw [← map_add, key, map_add, map_add, map_add, add_sub_add_comm]
        exact add_mem (hg a) (hg b)
      map_smul' := fun r a => by
        rw [RingHom.id_apply, ← map_smul, key, hφs, hφs, hks, ← map_sub]
        exact hs r _ (hg a) }
  refine ⟨N.liftQ g0 fun a ha => ?_, fun a b => key a b⟩
  change N.mkQ (g a) = 0
  rw [← map_zero N.mkQ, key, map_zero, sub_zero]
  exact hkC _ ((hN a).2 ha)

theorem exists_induced_equiv (N : Submodule R L) (φ : L →+ A) (s : R → A →+ A) (H C : AddSubgroup A)
    (hφs : ∀ r a, φ (r • a) = s r (φ a)) (hs : ∀ r, ∀ z ∈ C, s r z ∈ C) (hφ : ∀ a, φ a ∈ H)
    (hN : ∀ a, φ a ∈ C ↔ a ∈ N) (hon : ∀ z ∈ H, ∃ a, z - φ a ∈ C)
    (k : A →+ A) (hks : ∀ r z, k (s r z) = s r (k z)) (hkH : ∀ z ∈ H, k z ∈ H) (hkC : ∀ z ∈ C, k z ∈ C)
    (k' : A →+ A) (hks' : ∀ r z, k' (s r z) = s r (k' z)) (hkH' : ∀ z ∈ H, k' z ∈ H) (hkC' : ∀ z ∈ C, k' z ∈ C)
    (h1 : ∀ z, k (k' z) = z) (h2 : ∀ z, k' (k z) = z) :
    ∃ γ : (L ⧸ N) ≃ₗ[R] (L ⧸ N), ∀ a b, γ (N.mkQ a) = N.mkQ b ↔ k (φ a) - φ b ∈ C := by
  obtain ⟨f, hf⟩ := exists_induced N φ s H C hφs hs hφ hN hon k hks hkH hkC
  obtain ⟨f', hf'⟩ := exists_induced N φ s H C hφs hs hφ hN hon k' hks' hkH' hkC'
  refine ⟨LinearEquiv.ofLinearMap f f' ?_ ?_, hf⟩
  · refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := N.mkQ_surjective q
    obtain ⟨b, hb⟩ := N.mkQ_surjective (f' (N.mkQ a))
    have h := neg_mem (hkC _ ((hf' a b).1 hb.symm))
    rw [map_sub, h1, neg_sub] at h
    rw [LinearMap.comp_apply, ← hb]
    exact (hf b a).2 h
  · refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := N.mkQ_surjective q
    obtain ⟨b, hb⟩ := N.mkQ_surjective (f (N.mkQ a))
    have h := neg_mem (hkC' _ ((hf a b).1 hb.symm))
    rw [map_sub, h2, neg_sub] at h
    rw [LinearMap.comp_apply, ← hb]
    exact (hf' b a).2 h

end Abstract

section Space

variable {D : D7} (V : HSp D)

noncomputable def halfHom (b : 𝓞 D.host.E) :
    (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddMonoidHom.mk' (halfVec V b) fun _ _ => funext fun _ => mul_add _ _ _

theorem halfVec_eq (b : 𝓞 D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    halfVec V b z = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • z := rfl

theorem mulVec_halfVec (m : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) (b : 𝓞 D.host.E)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) : m *ᵥ halfVec V b z = halfVec V b (m *ᵥ z) := by
  rw [halfVec_eq, halfVec_eq, Matrix.mulVec_smul]

theorem map_closure_mem (I : Ideal (𝓞 D.host.E))
    (k : (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E))
    (hks : ∀ r z, k (halfVec V r z) = halfVec V r (k z)) (hk : ∀ z ∈ latGHat V 1, k z ∈ latGHat V 1) :
    ∀ z ∈ AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z},
      k z ∈ AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z} := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, z, hz, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨b, hb, k z, hk z hz, hks b z⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

end Space

theorem exists_levGrp_induced : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ κ ∈ GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1, ∃ γ : GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.LevGrp Dw l, ∀ a : Dw.La, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι (liftLa γ a)) ∈ AddSubgroup.closure {u | ∃ b ∈ l.Mb, ∃ z ∈ latGHat V 1, u = halfVec V b z} := by
  intro D V H Dw l ι hι κ hκ
  obtain ⟨hfg, hsp, -, -, hhat, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hMmem : (l.M : 𝓞 D.host.E) ∈ l.Mb := by
    have h : (l.M : 𝓞 D.host.E) ∈ Ideal.span {(l.M : 𝓞 D.host.E)} := Ideal.mem_span_singleton_self _
    rw [← l.prod] at h
    exact Ideal.mul_le_left h
  have hMb : l.Mb ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hMmem
    exact hM0.ne' (Nat.cast_eq_zero.1 hMmem)
  have hκ1 : ∀ z ∈ latGHat V 1, (finHom V κ).1 *ᵥ z ∈ latGHat V 1 :=
    (GlobalTheory.Member.AALev.congruences_agree D V κ).1.2 hκ.2
  have hκ0 : ∀ z ∈ latHat V, (finHom V κ).1 *ᵥ z ∈ latHat V := by
    intro z hz
    obtain ⟨y, hy, e⟩ := hκ.2 z hz
    rw [one_smul, sub_eq_iff_eq_add] at e
    rw [e]
    exact add_mem hy hz
  have hκ2 : ∀ z ∈ latGHat V 1, (finHom V κ⁻¹).1 *ᵥ z ∈ latGHat V 1 :=
    (GlobalTheory.Member.AALev.congruences_agree D V κ⁻¹).1.2 fun z hz =>
      ⟨_, sub_mem (GlobalTheory.RecDict.finHom_inv_mulVec_mem V κ hκ0 z hz) hz, (one_smul _ _).symm⟩
  let φ : Dw.La →+ (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (fun a => finVec V (ι a)) fun a b => by
      rw [map_add]
      exact GlobalTheory.Member.AALev.fv_add _ _
  have hmem : ∀ a, ι a ∈ latG V 1 := fun a => hι.2 ▸ LinearMap.mem_range_self ι a
  have hsH : ∀ r, ∀ z ∈ latGHat V 1, halfHom V r z ∈ latGHat V 1 := by
    intro r z hz
    rw [hhat] at hz ⊢
    exact GlobalTheory.Member.AALev.hat_smul_int (latG V 1) r hz
  obtain ⟨γ, hγ⟩ := exists_induced_equiv (l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) φ (halfHom V) (latGHat V 1)
    (AddSubgroup.closure {u | ∃ b ∈ l.Mb, ∃ z ∈ latGHat V 1, u = halfVec V b z})
    (fun r a => by
      change finVec V (ι (r • a)) = _
      rw [map_smul]
      exact GlobalTheory.Member.AALev.fv_smul (r : D.host.E) (ι a))
    (fun r => map_closure_mem V l.Mb (halfHom V r) (fun _ _ => funext fun _ => mul_left_comm _ _ _) (hsH r))
    (fun a => by
      rw [hhat]
      exact GlobalTheory.Member.AALev.fv_mem_hat _ (hmem a))
    (fun a => by
      refine (GlobalTheory.T.rationalVector_mem_ideal_completedLattice_iff D V l.Mb hMb (ι a)).trans ?_
      rw [← hι.2, LinearMap.range_eq_map, ← Submodule.map_smul'']
      constructor
      · rintro ⟨x, hx, e⟩
        exact hι.1 e ▸ hx
      · exact fun h => ⟨a, h, rfl⟩)
    (fun z hz => by
      rw [hhat] at hz
      obtain ⟨x, hx, w, hw, e⟩ :=
        (GlobalTheory.AdLat.hat_rational_points_and_approx _ _ _ _ hfg hsp).2.1 l.M hM0 z hz
      rw [← hι.2] at hx
      obtain ⟨a, rfl⟩ := hx
      rw [← hhat] at hw
      refine ⟨a, AddSubgroup.subset_closure ⟨_, hMmem, w, hw, ?_⟩⟩
      rw [e]
      refine (add_sub_cancel_left _ _).trans ?_
      rw [halfVec_eq, ← Nat.cast_smul_eq_nsmul (Af D.host.F ⊗[D.host.F] D.host.E)]
      congr 1
      exact (map_natCast ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F)
        (B := D.host.E)).toRingHom.comp (algebraMap (𝓞 D.host.E) D.host.E)) l.M).symm)
    (Matrix.mulVecLin (finHom V κ).1).toAddMonoidHom (mulVec_halfVec V _) hκ1
    (map_closure_mem V l.Mb _ (mulVec_halfVec V _) hκ1)
    (Matrix.mulVecLin (finHom V κ⁻¹).1).toAddMonoidHom (mulVec_halfVec V _) hκ2
    (map_closure_mem V l.Mb _ (mulVec_halfVec V _) hκ2)
    (fun z => by
      change (finHom V κ).1 *ᵥ ((finHom V κ⁻¹).1 *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, map_inv, Units.mul_inv, Matrix.one_mulVec])
    (fun z => by
      change (finHom V κ⁻¹).1 *ᵥ ((finHom V κ).1 *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec])
  exact ⟨γ, fun a => (hγ a _).1 (liftLa_spec γ a).symm⟩

end GlobalTheory.StabInduce
