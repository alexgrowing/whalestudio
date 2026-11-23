import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.LcFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.Integ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.LcFinAlt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationEqOneOfMemInvMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCupProductCoboundaryTheorem

open GlobalTheory.KZ GlobalTheory.K4 Polynomial UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PE

namespace UpperTheory.V.Z.Kato.Sym.PE

private def FinalTheorems : Prop :=
  ∀ (k F Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field Ω] [Algebra F (RatFunc k)] [Algebra (RatFunc k) Ω] [Algebra F Ω] [IsScalarTower F (RatFunc k) Ω] [Algebra k[X] Ω] [IsScalarTower k[X] (RatFunc k) Ω] [IsAlgClosure (RatFunc k) Ω] [Algebra.IsAlgebraic F Ω] (N : ℕ) [NeZero N] (ζ : Ω), IsPrimitiveRoot ζ N → ∀ (U : Subgroup (Ω ≃ₐ[F] Ω)), IsOpen (U : Set (Ω ≃ₐ[F] Ω)) → ∀ α β : Ω, α ≠ 0 → β ≠ 0 → IsIntegral k[X] α → IsIntegral k[X] α⁻¹ → IsIntegral k[X] β → IsIntegral k[X] β⁻¹ → (∀ g ∈ U, g (α ^ N) = α ^ N ∧ g (β ^ N) = β ^ N) → ∃ η₀ : (Ω ≃ₐ[F] Ω) → ZMod N, IsLocallyConstant (fun g : ↥(GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U) => η₀ g) ∧ (∀ g ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, ∀ h ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, GlobalTheory.NeedB.kum (N := N) ζ α g * GlobalTheory.NeedB.kum ζ β h = η₀ h - η₀ (g * h) + η₀ g) ∧ ∀ r ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, ∀ B : ValuationSubring Ω, (∀ p : k[X], algebraMap k[X] Ω p ∈ B) → GlobalTheory.NeedB.Inert B r → η₀ r = 0 ∧ r α = α ∧ r β = β

private theorem existsUnique_eq_primitiveRoot_pow_mul_of_pow_eq {E : Type} [Field E] {m : ℕ} [NeZero m] {ζ a c : E}
    (hζ : IsPrimitiveRoot ζ m) (ha : a ≠ 0) (hc : c ^ m = a ^ m) :
    ∃! i : ZMod m, c = ζ ^ i.val * a := by
  have h1 : (c / a) ^ m = 1 := by rw [div_pow, hc, div_self (pow_ne_zero _ ha)]
  obtain ⟨k, hk, hk'⟩ := hζ.eq_pow_of_pow_eq_one h1
  have hck : c = ζ ^ k * a := by rw [hk', div_mul_cancel₀ _ ha]
  refine ⟨(k : ZMod m), ?_, ?_⟩
  · show c = ζ ^ (k : ZMod m).val * a
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
    exact hck
  · intro j hj
    have e : ζ ^ j.val = ζ ^ k := mul_right_cancel₀ ha (hj.symm.trans hck)
    have := hζ.pow_inj (ZMod.val_lt j) hk e
    rw [← ZMod.natCast_zmod_val j, this]

private theorem etaEx_of (hS : FinalTheorems) (hA : Alg) (hI : Integ) (hL : LcFin) : EtaEx := by
  intro Ω _ _ _ ε X m hm u v a b hu hv ha hb
  obtain ⟨φ, hφ, halg⟩ := hA Ω ε X
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap ℚ Ω).injective).mp inferInstance
  haveI : NeZero m := ⟨hm.ne'⟩
  letI alg1 : Algebra (RatFunc Ω) (Kb X) := φ.toAlgebra
  letI alg2 : Algebra (Polynomial Ω) (Kb X) := (pj X).toAlgebra
  haveI tw : IsScalarTower (Polynomial Ω) (RatFunc Ω) (Kb X) :=
    IsScalarTower.of_algebraMap_eq fun p => (hφ p).symm
  haveI : IsAlgClosed (Kb X) := by unfold Kb; infer_instance
  haveI : IsAlgClosure (RatFunc Ω) (Kb X) := ⟨inferInstance, halg⟩
  haveI : IsGalois (RatFunc Ω) (Kb X) := inferInstance
  let L := IntermediateField.adjoin (RatFunc Ω) ({io X u, io X v} : Set (Kb X))
  haveI : FiniteDimensional (RatFunc Ω) L :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (halg.isAlgebraic x).isIntegral)
  have hU : IsOpen (L.fixingSubgroup : Set (Kb X ≃ₐ[RatFunc Ω] Kb X)) :=
    IntermediateField.fixingSubgroup_isOpen L
  have hζ : IsPrimitiveRoot (zt X m) m :=
    (isPrimitiveRoot_eOm ε hm.ne').map_of_injective
      (f := (algebraMap X.K (Kb X)).comp (algebraMap Ω X.K)) (RingHom.injective _)
  obtain ⟨ha0, haI, haI'⟩ := hI Ω ε X m hm u a hu ha
  obtain ⟨hb0, hbI, hbI'⟩ := hI Ω ε X m hm v b hv hb
  have hinL : ∀ g ∈ L.fixingSubgroup, g (io X u) = io X u ∧ g (io X v) = io X v := by
    intro g hg
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff] at hg
    exact ⟨hg _ (IntermediateField.subset_adjoin _ _ (by simp)),
      hg _ (IntermediateField.subset_adjoin _ _ (by simp))⟩
  have hfix : ∀ g ∈ L.fixingSubgroup, g (a ^ m) = a ^ m ∧ g (b ^ m) = b ^ m := by
    intro g hg
    rw [ha, hb]
    exact hinL g hg
  obtain ⟨η₀, hlc, hcoc, hunr⟩ :=
    hS Ω (RatFunc Ω) (Kb X) m (zt X m) hζ L.fixingSubgroup hU a b ha0 hb0 haI haI' hbI hbI' hfix
  have hgeo : ∀ G : Kb X ≃ₐ[RatFunc Ω] Kb X, G ∈ GlobalTheory.K4.geo (RatFunc Ω) (RatFunc Ω) (Kb X) := by
    intro G
    unfold GlobalTheory.K4.geo
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨r, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    exact G.commutes r
  have hmem : ∀ G : Kb X ≃ₐ[RatFunc Ω] Kb X, G (io X u) = io X u → G (io X v) = io X v →
      G ∈ GlobalTheory.K4.geo (RatFunc Ω) (RatFunc Ω) (Kb X) ⊓ L.fixingSubgroup := by
    intro G hu' hv'
    refine Subgroup.mem_inf.mpr ⟨hgeo G, ?_⟩
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
    intro y hy
    have e := IntermediateField.adjoin_algHom_ext (RatFunc Ω)
      (φ₁ := (G.toAlgHom).comp L.val) (φ₂ := L.val) (by
        rintro x (rfl | rfl)
        · exact hu'
        · exact hv')
    exact AlgHom.congr_fun e ⟨y, hy⟩
  obtain ⟨B, hB⟩ := hL (RatFunc Ω) (Kb X) (ZMod m) _ (by
    have : GlobalTheory.K4.geo (RatFunc Ω) (RatFunc Ω) (Kb X) ⊓ L.fixingSubgroup = L.fixingSubgroup :=
      inf_eq_right.mpr fun G _ => hgeo G
    rw [this]
    exact hU) η₀ hlc
  have hcomm : ∀ g : RingAut (Kb X),
      (∀ c : Ω, g (io X (algebraMap Ω X.K c)) = io X (algebraMap Ω X.K c)) →
      g (io X X.jK) = io X X.jK → ∀ r, g (φ r) = φ r := by
    intro g h1 h2
    have e : (g.toRingHom.comp φ).comp (algebraMap (Polynomial Ω) (RatFunc Ω)) =
        φ.comp (algebraMap (Polynomial Ω) (RatFunc Ω)) := by
      apply Polynomial.ringHom_ext
      · intro c
        show g (φ (algebraMap (Polynomial Ω) (RatFunc Ω) (Polynomial.C c))) =
          φ (algebraMap (Polynomial Ω) (RatFunc Ω) (Polynomial.C c))
        rw [hφ]
        show g (io X (Polynomial.aeval X.jK (Polynomial.C c))) = io X (Polynomial.aeval X.jK (Polynomial.C c))
        rw [Polynomial.aeval_C]
        exact h1 c
      · show g (φ (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X)) =
          φ (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X)
        rw [hφ]
        show g (io X (Polynomial.aeval X.jK Polynomial.X)) = io X (Polynomial.aeval X.jK Polynomial.X)
        rw [Polynomial.aeval_X]
        exact h2
    have e2 := IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial Ω)) e
    intro r
    exact RingHom.congr_fun e2 r
  have hk : ∀ (g : RingAut (Kb X)) (G : Kb X ≃ₐ[RatFunc Ω] Kb X), (∀ x, G x = g x) →
      ∀ x : Kb X, x ≠ 0 → g (x ^ m) = x ^ m → ka X m x g = GlobalTheory.NeedB.kum (zt X m) x G := by
    intro g G hG x hx0 hxm
    obtain ⟨i, hi, huniq⟩ := existsUnique_eq_primitiveRoot_pow_mul_of_pow_eq (c := g x) hζ hx0 (by rw [← map_pow, hxm])
    unfold ka lg GlobalTheory.NeedB.kum
    rw [hG, dif_pos ⟨i, hi⟩]
    exact (huniq _ (Classical.epsilon_spec (p := fun j : ZMod m => g x = zt X m ^ j.val * x) ⟨i, hi⟩)).trans
      (huniq _ (Exists.choose_spec (⟨i, hi⟩ : ∃ j : ZMod m, g x = zt X m ^ j.val * x))).symm
  classical
  refine ⟨fun g => if hg : ∀ r, g (φ r) = φ r then η₀ (AlgEquiv.ofRingEquiv (f := g) hg) else 0,
    ?_, ?_, ?_⟩
  · intro g h hg hh
    unfold InU at hg hh
    obtain ⟨g1, g2, g3, g4⟩ := hg
    obtain ⟨h1, h2, h3, h4⟩ := hh
    have cg := hcomm g g1 g2
    have ch := hcomm h h1 h2
    have cgh : ∀ r, (g * h) (φ r) = φ r := fun r => by
      show g (h (φ r)) = φ r
      rw [ch, cg]
    have hGH : AlgEquiv.ofRingEquiv (f := g * h) cgh =
        AlgEquiv.ofRingEquiv (f := g) cg * AlgEquiv.ofRingEquiv (f := h) ch := by
      ext x
      rfl
    simp only [dif_pos cg, dif_pos ch, dif_pos cgh]
    rw [hGH, hk g (AlgEquiv.ofRingEquiv (f := g) cg) (fun _ => rfl) a ha0 (by rw [ha]; exact g3),
      hk h (AlgEquiv.ofRingEquiv (f := h) ch) (fun _ => rfl) b hb0 (by rw [hb]; exact h4)]
    exact hcoc _ (hmem _ g3 g4) _ (hmem _ h3 h4)
  · unfold LC
    refine ⟨B, ?_⟩
    intro h h' hh hh' hBB
    unfold InD at hh hh'
    have ch := hcomm h (fun c => hh _) (hh _)
    have ch' := hcomm h' (fun c => hh' _) (hh' _)
    simp only [dif_pos ch, dif_pos ch']
    exact hB _ (hmem _ (hh u) (hh v)) _ (hmem _ (hh' u) (hh' v)) hBB
  · unfold Unr
    intro B h hY hh hin
    unfold InD at hh
    unfold Tower.OverY at hY
    have ch := hcomm h (fun c => hh _) (hh _)
    simp only [dif_pos ch]
    refine (hunr (AlgEquiv.ofRingEquiv (f := h) ch) (hmem _ (hh u) (hh v)) B ?_ hin).1
    intro p
    show io X (Polynomial.aeval X.jK p) ∈ B
    have : Polynomial.aeval X.jK p ∈ B.comap (io X) := by
      refine Polynomial.induction_on p (fun c => ?_) (fun p q hp hq => ?_) (fun n c _ => ?_)
      · rw [Polynomial.aeval_C]
        exact hY.1 c
      · rw [map_add]
        exact add_mem hp hq
      · rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
        exact mul_mem (hY.1 c) (pow_mem hY.2 _)
    exact this

theorem etaEx : EtaEx := etaEx_of (GlobalTheory.K4.thmA_on_open_geo GlobalTheory.KummerCob.thmA) alg integ lcFin

end UpperTheory.V.Z.Kato.Sym.PE
