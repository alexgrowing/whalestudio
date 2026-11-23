import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgHomEqOrConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceCompletionEquivUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfSupportedAtSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteOfLocEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongOfLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceProjMemIntegersOfIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalCongInvMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompactOpenCongr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatCongruenceLeOpenSubgroupGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedNatCastAdicCompletionLeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalOfLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.LocCompSplit

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

def rtRep {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (S : Submodule ℂ (GAf L n → W))
    (hS : ∀ h, ∀ f ∈ S, NG.rt L n h f ∈ S) : Representation ℂ (GAf L n) S where
  toFun h := (NG.rt L n h).restrict (fun f hf => hS h f hf)
  map_one' := LinearMap.ext fun f => Subtype.ext (funext fun g => by
    show f.1 (g * 1) = f.1 g
    rw [mul_one])
  map_mul' x y := LinearMap.ext fun f => Subtype.ext (funext fun g => by
    show f.1 (g * (x * y)) = f.1 (g * x * y)
    rw [mul_assoc])

theorem rtRep_apply {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (S : Submodule ℂ (GAf L n → W))
    (hS : ∀ h, ∀ f ∈ S, NG.rt L n h f ∈ S) (h : GAf L n) (f : S) :
    ((rtRep S hS h f : S) : GAf L n → W) = NG.rt L n h f := rfl

def rtOf {n : ℕ} (π : NG.AutRep L n) : Representation ℂ (GAf L n) π.S := rtRep π.S π.irrS.1.stable

theorem isIrreducible_comp_of_surjective {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (φ : H →* G) (hφ : Function.Surjective φ) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ) := by
  obtain ⟨hnt, hρ⟩ := (GlobalTheory.CuspRep.isIrreducible_iff ρ).1 h
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨hnt, fun W hW => hρ W fun g v hv => ?_⟩
  obtain ⟨k, rfl⟩ := hφ g
  exact hW k v hv

theorem rtOf_irreducible {n : ℕ} (π : NG.AutRep L n) : (rtOf π).IsIrreducible := by
  refine (GlobalTheory.CuspRep.isIrreducible_iff (rtOf π)).2 ⟨Submodule.nontrivial_iff_ne_bot.2 π.irrS.2.1, fun W hW => ?_⟩
  have hsub : NG.IsSubrep π.ρ (W.map π.S.subtype) := by
    refine ⟨(Submodule.map_subtype_le _ _).trans π.irrS.1.le, ?_⟩
    rintro h _ ⟨f, hf, rfl⟩
    exact ⟨rtOf π h f, hW h f hf, rtRep_apply π.S π.irrS.1.stable h f⟩
  have hi := Submodule.map_injective_of_injective π.S.injective_subtype
  rcases π.irrS.2.2 (W.map π.S.subtype) hsub (Submodule.map_subtype_le _ _) with h | h
  · exact Or.inl (hi (h.trans (Submodule.map_bot _).symm))
  · exact Or.inr (hi (h.trans (Submodule.map_subtype_top _).symm))

theorem exists_local {n : ℕ} (π : NG.AutRep L n) (s : SplitPlace L)
    (e : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L)) →* GAf L n)
    (he1 : ∀ g, TrivOutside {s.v} (e g)) (he2 : ∀ g, s.loc n (e g) = g) :
    ∃ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))),
      ∃ T : σ.V →ₗ[ℂ] (GAf L n → π.W),
      Function.Injective T ∧ (∀ a, T a ∈ π.S) ∧ ∀ g a, T (σ.ρ g a) = NG.rt L n (e g) (T a) := by
  classical
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  have hirrG : (rtOf π).IsIrreducible := rtOf_irreducible π
  have hlev : ∀ f : π.S, ∃ N, 0 < N ∧ ∀ κ, NG.Cong L n N κ → (rtOf π) κ f = f := by
    intro f
    obtain ⟨-, N, hN, hf⟩ := π.irrS.1.le f.2
    exact ⟨N, hN, fun κ hκ => Subtype.ext (funext fun g => hf κ hκ g)⟩
  have hcongE : ∀ (N : ℕ), 0 < N → ∀ g : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L)),
      (∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) _) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j) ≤
          Valued.v ((N : s.v.adicCompletion (NumberField.maximalRealSubfield L)))) →
      (∀ i j, Valued.v (((g⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j) ≤
          Valued.v ((N : s.v.adicCompletion (NumberField.maximalRealSubfield L)))) →
      NG.Cong L n N (e g) := by
    intro N hN g h1 h2
    refine GlobalTheory.CongSplit.cong_of_loc L n s N hN (e g) (he1 g) (fun i j => ?_) (fun i j => ?_)
    · rw [he2]; exact h1 i j
    · rw [map_inv, he2]; exact h2 i j
  have hcpt : ∀ N, 0 < N → ∃ K : Subgroup (GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))),
      IsOpen (K : Set (GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L)))) ∧ IsCompact (K : Set (GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L)))) ∧ ∀ g ∈ K, NG.Cong L n N (e g) := by
    intro N hN
    obtain ⟨K, hKo, hKc, hK⟩ := GlobalTheory.GLCongrCptOpen.exists_compactOpen_congr _ s.v n (N : s.v.adicCompletion (NumberField.maximalRealSubfield L))
      (by
        rw [← map_natCast (algebraMap (NumberField.maximalRealSubfield L)
          (s.v.adicCompletion (NumberField.maximalRealSubfield L)))]
        exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 hN.ne'))
    exact ⟨K, hKo, hKc, fun g hg => hcongE N hN g (hK g hg) (hK g⁻¹ (K.inv_mem hg))⟩
  have hsm : GlobalTheory.PRep.IsSmooth ((rtOf π).comp e) := by
    intro f
    obtain ⟨N, hN, hf⟩ := hlev f
    obtain ⟨K, hKo, -, hK⟩ := hcpt N hN
    have hle : K ≤ GlobalTheory.CuspRep.LocEx.stab ((rtOf π).comp e) f := fun g hg => hf _ (hK g hg)
    exact Subgroup.isOpen_mono hle hKo
  have hcomm : ∀ (x : GAf L n) g, Commute ((e (s.loc n x))⁻¹ * x) (e g) := fun x g =>
    GlobalTheory.SplitLocComm.commute_of_loc_eq_one L n s _ _ (by rw [map_mul, map_inv, he2, inv_mul_cancel]) (he1 g)
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.irrS.2.1
  obtain ⟨v0, hv0e⟩ : ∃ v0 : π.S, v0 = ⟨φ, hφ⟩ := ⟨_, rfl⟩
  have hv0 : v0 ≠ 0 := fun h => h0 (by rw [hv0e] at h; exact congrArg Subtype.val h)
  obtain ⟨N0, hN0, hv0N⟩ := hlev v0
  obtain ⟨K0, hK0o, hK0c, hK0⟩ := hcpt N0 hN0
  have hT : ∀ (x : GAf L n) g (y : π.S),
      (rtOf π) ((e (s.loc n x))⁻¹ * x) (((rtOf π).comp e) g y) = ((rtOf π).comp e) g ((rtOf π) ((e (s.loc n x))⁻¹ * x) y) := fun x g y => by
    show (rtOf π) _ ((rtOf π) (e g) y) = (rtOf π) (e g) ((rtOf π) _ y)
    rw [← Module.End.mul_apply, ← map_mul, (hcomm x g).eq, map_mul, Module.End.mul_apply]
  have hnull : ∀ x, ∀ y ∈ GlobalTheory.CuspRep.LocEx.nullPart ((rtOf π).comp e) K0, (rtOf π) x y ∈ GlobalTheory.CuspRep.LocEx.nullPart ((rtOf π).comp e) K0 := by
    intro x y hy
    have h1 := GlobalTheory.CuspRep.LocEx.nullPart_act ((rtOf π).comp e) K0 (s.loc n x)
      (GlobalTheory.CuspRep.LocEx.nullPart_comm ((rtOf π).comp e) K0 ((rtOf π) ((e (s.loc n x))⁻¹ * x)) (hT x) hy)
    have e1 : (rtOf π) x y = ((rtOf π).comp e) (s.loc n x) ((rtOf π) ((e (s.loc n x))⁻¹ * x) y) := by
      show _ = (rtOf π) (e (s.loc n x)) _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    rw [e1]
    exact h1
  have hv0K : v0 ∈ GlobalTheory.PRep.fixed ((rtOf π).comp e) K0 := GlobalTheory.CuspRep.LocEx.mem_fix.2 fun k hk => hv0N _ (hK0 k hk)
  have h2 : ∀ W : Submodule ℂ π.S, (∀ g, ∀ v ∈ W, ((rtOf π).comp e) g v ∈ W) → W ⊓ GlobalTheory.PRep.fixed ((rtOf π).comp e) K0 = ⊥ → W = ⊥ := by
    intro W hW h
    rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hirrG).2 (GlobalTheory.CuspRep.LocEx.nullPart ((rtOf π).comp e) K0) hnull with h1 | h1
    · exact le_bot_iff.1 (h1 ▸ GlobalTheory.CuspRep.LocEx.le_nullPart hsm hK0c W hW h)
    · exact absurd (GlobalTheory.CuspRep.LocEx.eq_zero_of_mem_nullPart hsm hK0c hv0K (h1 ▸ Submodule.mem_top)) hv0
  obtain ⟨U, hUe⟩ : ∃ U : Submodule ℂ π.S, U = ⨅ (κ : GAf L n) (_ : NG.Cong L n N0 κ ∧ s.loc n κ = 1),
      LinearMap.ker ((rtOf π) κ - 1) := ⟨_, rfl⟩
  have hmemU : ∀ f, f ∈ U ↔ ∀ κ, NG.Cong L n N0 κ → s.loc n κ = 1 → (rtOf π) κ f = f := by
    intro f
    simp only [hUe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact ⟨fun h κ h1 h2 => h κ ⟨h1, h2⟩, fun h κ hκ => h κ hκ.1 hκ.2⟩
  have hU : ∀ g, ∀ f ∈ U, ((rtOf π).comp e) g f ∈ U := by
    intro g f hf
    rw [hmemU] at hf ⊢
    intro κ h1 h2
    have hc : Commute κ (e g) := GlobalTheory.SplitLocComm.commute_of_loc_eq_one L n s κ (e g) h2 (he1 g)
    show (rtOf π) κ ((rtOf π) (e g) f) = (rtOf π) (e g) f
    rw [← Module.End.mul_apply, ← map_mul, hc.eq, map_mul, Module.End.mul_apply, hf κ h1 h2]
  have hU0 : U ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨v0, (hmemU v0).2 fun κ h1 _ => hv0N κ h1, hv0⟩
  have hfin : ∀ K' : Subgroup (GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))),
      IsOpen (K' : Set (GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L)))) → FiniteDimensional ℂ ↥(U ⊓ GlobalTheory.PRep.fixed ((rtOf π).comp e) K') := by
    intro K' hK'
    obtain ⟨M, hM, hMK⟩ := GlobalTheory.exists_nat_congruence_le_open_subgroup_GL _ s.v n K' hK'
    have hN' : 0 < N0 * M := Nat.mul_pos hN0 hM
    have hvM : Valued.v (((N0 * M : ℕ) : s.v.adicCompletion (NumberField.maximalRealSubfield L))) ≤
        Valued.v ((M : s.v.adicCompletion (NumberField.maximalRealSubfield L))) := by
      rw [Nat.cast_mul, map_mul]
      exact mul_le_of_le_one_left' (GlobalTheory.valued_natCast_adicCompletion_le_one _ s.v N0)
    have hvN : Valued.v (((N0 * M : ℕ) : s.v.adicCompletion (NumberField.maximalRealSubfield L))) ≤
        Valued.v ((N0 : s.v.adicCompletion (NumberField.maximalRealSubfield L))) := by
      rw [Nat.cast_mul, map_mul]
      exact mul_le_of_le_one_right' (GlobalTheory.valued_natCast_adicCompletion_le_one _ s.v M)
    have hcong1 : NG.Cong L n (N0 * M) 1 := by
      refine ⟨(Umax L n).one_mem, fun i j => ⟨0, Subring.zero_mem _, ?_⟩⟩
      simp
    have hkey : ∀ f ∈ U ⊓ GlobalTheory.PRep.fixed ((rtOf π).comp e) K', ∀ κ, NG.Cong L n (N0 * M) κ → (rtOf π) κ f = f := by
      intro f hf κ hκ
      obtain ⟨hfU, hfK⟩ := Submodule.mem_inf.1 hf
      have hκinv : NG.Cong L n (N0 * M) κ⁻¹ := by
        simpa using GlobalTheory.principalCong_inv_mul L n (N0 * M) κ 1 hκ hcong1
      have hl1 := GlobalTheory.splitPlace_loc_congr_one L n s (N0 * M) κ hκ
      have hl2 := GlobalTheory.splitPlace_loc_congr_one L n s (N0 * M) κ⁻¹ hκinv
      have hlK : s.loc n κ ∈ K' := hMK _ (fun i j => (hl1 i j).trans hvM)
        (fun i j => by rw [← map_inv]; exact (hl2 i j).trans hvM)
      have hce : NG.Cong L n N0 (e (s.loc n κ)) := hcongE N0 hN0 _ (fun i j => (hl1 i j).trans hvN)
        (fun i j => by rw [← map_inv]; exact (hl2 i j).trans hvN)
      have hκ0 : NG.Cong L n N0 ((e (s.loc n κ))⁻¹ * κ) := GlobalTheory.principalCong_inv_mul L n N0 _ _ hce (NG.Cong.of_mul_left L n hκ)
      have hl0 : s.loc n ((e (s.loc n κ))⁻¹ * κ) = 1 := by rw [map_mul, map_inv, he2, inv_mul_cancel]
      have e1 : (rtOf π) κ f = (rtOf π) (e (s.loc n κ)) ((rtOf π) ((e (s.loc n κ))⁻¹ * κ) f) := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      rw [e1, (hmemU f).1 hfU _ hκ0 hl0]
      exact GlobalTheory.CuspRep.LocEx.mem_fix.1 hfK _ hlK
    have hfd := GlobalTheory.LevelForms.finiteDimensional_of_level L n π.ρ (N0 * M) hN' ((U ⊓ GlobalTheory.PRep.fixed ((rtOf π).comp e) K').map π.S.subtype) (by
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨π.irrS.1.le f.2, fun κ hκ => congrArg Subtype.val (hkey f hf κ hκ)⟩)
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ π.S.injective_subtype _).symm
  obtain ⟨σ, ⟨f, hf0, hf⟩, hadm⟩ := GlobalTheory.CuspRep.LocEx.exists_irred hsm hK0o h2 U hU hU0 hfin
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    rcases ((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 σ.irred).2 (LinearMap.ker f) (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hf, hv, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hf0
  refine ⟨⟨σ.V, σ.ρ, hadm.1, σ.irred⟩, π.S.subtype ∘ₗ f, π.S.injective_subtype.comp hinj, fun a => (f a).2,
    fun g a => ?_⟩
  show ((f (σ.ρ g a) : π.S) : GAf L n → π.W) = _
  rw [hf]
  rfl

end GlobalTheory.LocCompSplit

namespace GlobalTheory.LocCompSplit

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem gl_map_symm_map {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (i : A ≃+* B) (g : GL (Fin n) A) :
    Matrix.GeneralLinearGroup.map i.symm.toRingHom (Matrix.GeneralLinearGroup.map i.toRingHom g) = g := by
  ext
  simp

theorem gl_map_map_symm {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (i : A ≃+* B) (g : GL (Fin n) B) :
    Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) = g := by
  ext
  simp

theorem exists_isLocS {n : ℕ} (π : NG.AutRep L n) (s : SplitPlace L) : ∃ σ, IsLocS π.S s σ := by
  obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc L n s
  obtain ⟨i, hi, hi', hiL⟩ := GlobalTheory.SplitComplHomeo.exists_complEquiv L s
  obtain ⟨σ₀, T, hTi, hTm, hTe⟩ := exists_local π s e he1 he2
  let ψ : GL (Fin n) (s.w.adicCompletion L) →* GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L)) :=
    Matrix.GeneralLinearGroup.map i.symm.toRingHom
  have hψc : Continuous ψ := Continuous.units_map _ (continuous_id.matrix_map hi')
  have hψs : Function.Surjective ψ := fun g => ⟨Matrix.GeneralLinearGroup.map i.toRingHom g, gl_map_symm_map i g⟩
  let σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)) :=
    ⟨σ₀.V, σ₀.ρ.comp ψ, fun v => (σ₀.smooth v).preimage hψc, isIrreducible_comp_of_surjective σ₀.ρ ψ hψs σ₀.irr⟩
  refine ⟨σ, i, T, hi, hiL, hTi, hTm, fun x hx a => ?_⟩
  show T (σ₀.ρ (ψ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x))) a) = _
  rw [gl_map_symm_map i, hTe, GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq L n s _ _ (he1 _) hx (he2 _)]

theorem isLocS_unique {n : ℕ} (π π' : NG.AutRep L n) (s : SplitPlace L)
    (σ σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (hπ : π.Iso π')
    (hσ : IsLocS π.S s σ) (hσ' : IsLocS π'.S s σ') : σ'.cl = σ.cl := by
  classical
  obtain ⟨i, T, hi, hiL, hTi, hTm, hTe⟩ := hσ
  obtain ⟨i', T', hi', hiL', hTi', hTm', hTe'⟩ := hσ'
  obtain rfl := GlobalTheory.splitPlace_completion_equiv_unique L s i' i hi' hi hiL' hiL
  obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc L n s
  obtain ⟨-, T0, hT0⟩ := hπ
  let φ : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L)) →* GL (Fin n) (s.w.adicCompletion L) :=
    Matrix.GeneralLinearGroup.map i'.toRingHom
  have hφ : Function.Surjective φ := fun h => ⟨Matrix.GeneralLinearGroup.map i'.symm.toRingHom h, gl_map_map_symm i' h⟩
  have hirr : ∀ (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), Representation.IsIrreducible (τ.ρ.comp φ) :=
    fun τ => isIrreducible_comp_of_surjective τ.ρ φ hφ τ.irr
  have hloc : ∀ g, Matrix.GeneralLinearGroup.map i'.toRingHom (s.loc n (e g)) = φ g := fun g => by rw [he2]
  let F : Representation.IntertwiningMap (σ.ρ.comp φ) ((rtOf π).comp e) :=
    ⟨T.codRestrict π.S hTm, fun g => LinearMap.ext fun a => Subtype.ext (by
      show T (σ.ρ (φ g) a) = NG.rt L n (e g) (T a)
      rw [← hloc]
      exact hTe (e g) (he1 g) a)⟩
  have hT0s : ∀ (h : GAf L n) (y : π'.S) (hy : NG.rt L n h (y : GAf L n → π'.W) ∈ π'.S),
      T0.symm ⟨NG.rt L n h y, hy⟩ = rtOf π h (T0.symm y) := by
    intro h y hy
    apply T0.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [hT0 h (T0.symm y) (rtOf π h (T0.symm y)) rfl, LinearEquiv.apply_symm_apply]
  have hT'e : ∀ g a, T' (σ'.ρ (φ g) a) = NG.rt L n (e g) (T' a) := fun g a => by
    rw [← hloc]
    exact hTe' (e g) (he1 g) a
  let F' : Representation.IntertwiningMap (σ'.ρ.comp φ) ((rtOf π).comp e) :=
    ⟨T0.symm.toLinearMap ∘ₗ T'.codRestrict π'.S hTm', fun g => LinearMap.ext fun a => by
      have h1 : (⟨T' (σ'.ρ (φ g) a), hTm' _⟩ : π'.S) = ⟨NG.rt L n (e g) (T' a), (hT'e g a) ▸ hTm' _⟩ :=
        Subtype.ext (hT'e g a)
      show T0.symm ⟨T' (σ'.ρ (φ g) a), hTm' _⟩ = rtOf π (e g) (T0.symm ⟨T' a, hTm' a⟩)
      rw [h1]
      exact hT0s (e g) ⟨T' a, hTm' a⟩ _⟩
  have hnt : ∀ (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), Nontrivial τ.V :=
    fun τ => ((GlobalTheory.CuspRep.isIrreducible_iff τ.ρ).1 τ.irr).1
  have hF0 : F ≠ 0 := by
    intro h
    obtain ⟨a, ha⟩ := @exists_ne σ.V (hnt σ) 0
    apply ha
    apply hTi
    rw [map_zero]
    exact congrArg Subtype.val (DFunLike.congr_fun h a)
  have hF'0 : F' ≠ 0 := by
    intro h
    obtain ⟨a, ha⟩ := @exists_ne σ'.V (hnt σ') 0
    apply ha
    apply hTi'
    rw [map_zero]
    have h2 := DFunLike.congr_fun h a
    have h3 : T0.symm ⟨T' a, hTm' a⟩ = 0 := h2
    have h4 := congrArg (fun y => ((T0 y : π'.S) : GAf L n → π'.W)) h3
    simpa using h4
  have hcomm : ∀ (x : GAf L n), ∃ u, ∀ y, Commute ((e u)⁻¹ * x) (e y) := fun x =>
    ⟨s.loc n x, fun y => GlobalTheory.SplitLocComm.commute_of_loc_eq_one L n s _ _ (by rw [map_mul, map_inv, he2, inv_mul_cancel]) (he1 y)⟩
  obtain ⟨-, hiso⟩ := GlobalTheory.CuspRep.CompUniq.isotypic (GAf L n) _ π.S σ.V σ'.V (rtOf π) e (σ.ρ.comp φ) (σ'.ρ.comp φ)
    (rtOf_irreducible π) (hirr σ) (hirr σ') hcomm F hF0
  obtain ⟨E⟩ := hiso F' hF'0
  let E2 : σ.ρ.Equiv σ'.ρ := Representation.Equiv.mk' ⟨E.toLinearEquiv.toLinearMap, fun h => by
      obtain ⟨g, rfl⟩ := hφ h
      exact E.isIntertwining' g⟩ E.invFun E.left_inv E.right_inv
  exact GlobalTheory.SmGL.IrrRep.cl_eq_iff.2 ⟨E2.symm⟩

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L),
    ∃ σ, IsLocS π.S s σ ∧ ∀ (π' : NG.AutRep L n) (s' : SplitPlace L) (h : s'.w = s.w) σ', π.Iso π' →
      IsLocS π'.S s' σ' → HEq σ'.cl σ.cl := by
  intro L _ _ _ n π s
  obtain ⟨σ, hσ⟩ := exists_isLocS π s
  refine ⟨σ, hσ, fun π' s' h σ' hπ hσ' => ?_⟩
  obtain rfl := GlobalTheory.SplitPlaceExt.eq_of_w_eq L s s' h
  exact heq_of_eq (isLocS_unique π π' s' σ σ' hπ hσ hσ')

end GlobalTheory.LocCompSplit
