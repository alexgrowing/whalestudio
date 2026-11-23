import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPair
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpen
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairA
import ReciprocityTheory.GroupCohomology.CupCor
import ReciprocityTheory.GroupCohomology.ContractNthCastAddCastSucc
import ReciprocityTheory.GroupCohomology.ResNormalHolds

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

section general

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

noncomputable def smulBil (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] : V →ₗ[R] R →ₗ[R] V :=
  (LinearMap.lsmul R V).flip

noncomputable def smulPairing (M : TRep ℤ G) [DiscreteTopology M.V] : Pairing M (trivRep G ℤ) M where
  β := @smulBil ℤ M.V _ _ M.mod
  cont := continuous_of_discreteTopology
  equiv g m n := (@LinearMap.map_smul ℤ M.V M.V _ _ _ M.mod M.mod (M.rho g) (show ℤ from n) m).symm

theorem smulPairing_apply (M : TRep ℤ G) [DiscreteTopology M.V] (x : M.V) (n : ℤ) :
    (smulPairing M).β x n = n • x := int_smul_eq_zsmul M.mod n x

theorem exists_int_cocycle (t : G → ℚ) (m : (Fin 2 → G) → ℤ) (ht : IsLocallyConstant t)
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) :
    ∃ (y : (trivRep G ℤ).coch.X 2), (trivRep G ℤ).coch.d 2 y = 0 ∧ ∀ g, y.1 g = m g := by
  obtain ⟨z, hz, hzm⟩ := exists_defect_cocycle (trivRep G ℤ) (a := (1 : ℤ)) (fun _ => rfl) ht hm
  exact ⟨z, hz, fun g => (hzm g).trans (mul_one (m g))⟩

theorem cupFun_zero_two {M N P : TRep ℤ G} (b : Pairing M N P) (f : (Fin 0 → G) → M.V) (f' : (Fin 2 → G) → N.V)
    (g : Fin (0 + 2) → G) : cupFun b 0 2 f f' g = b.β (f ![]) (f' g) := by
  unfold cupFun
  rw [show (fun i : Fin 0 => g (Fin.castAdd 2 i)) = ![] from Subsingleton.elim _ _,
    show (fun j : Fin 2 => g (Fin.natAdd 0 j)) = g from funext fun j => congrArg g (Fin.ext (by simp))]
  simp

theorem trep_dn_zero {R : Type} [CommRing R] (M : TRep R G) (f : (Fin 0 → G) → M.V) (v : Fin 1 → G) :
    ReciprocityTheory.Gal.dn M.rho 0 f v = M.rho (v 0) (f ![]) - f ![] :=
  LowDeg.dn_zero_apply M.rho f v

theorem cor_smul_cocycle (M : TRep ℤ G) [DiscreteTopology M.V] (U : Subgroup G) [U.FiniteIndex]
    (hU : IsOpen (U : Set G)) (cor : Cx.Hom (M.resSub U).coch M.coch) (hcor : IsCor M U cor)
    (x : M.V) (hx : ∀ g ∈ U, M.rho g x = x) (x' : M.V) (hx' : corFun M U 0 (fun _ => x) ![] = x')
    (y : (trivRep G ℤ).coch.X 2) (hy : (trivRep G ℤ).coch.d 2 y = 0)
    (zU : (M.resSub U).coch.X 2) (hzU : (M.resSub U).coch.d 2 zU = 0)
    (hzU1 : ∀ g, zU.1 g = (show ℤ from y.1 fun i => (g i : G)) • x)
    (z : M.coch.X 2) (hz : M.coch.d 2 z = 0) (hz1 : ∀ g, z.1 g = (show ℤ from y.1 g) • x') :
    cor.H 2 ((M.resSub U).coch.cls 2 zU hzU) = M.coch.cls 2 z hz := by
  let bP := smulPairing M
  let bU : Pairing (M.resSub U) ((trivRep G ℤ).resSub U) (M.resSub U) :=
    ⟨bP.β, bP.cont, fun g m n => bP.equiv g.1 m n⟩
  let x0 : (M.resSub U).coch.X 0 := ⟨fun _ => x, continuous_const⟩
  have hx0 : (M.resSub U).coch.d 0 x0 = 0 := by
    refine Subtype.ext (funext fun g => ?_)
    refine (trep_dn_zero (M.resSub U) x0.1 g).trans ?_
    show M.rho (g 0).1 x - x = 0
    rw [hx _ (g 0).2, sub_self]
  have hry : ((trivRep G ℤ).resSub U).coch.d 2
      ((Pair.res (trivRep G ℤ) U.subtype continuous_subtype_val).hom.f 2 y) = 0 := Cx.Hom.d_f_eq_zero _ hy
  have hcx : M.coch.d 0 (cor.f 0 x0) = 0 := Cx.Hom.d_f_eq_zero _ hx0
  have key : cor.H (0 + 2) (cupCoh bU 0 2 ((M.resSub U).coch.cls 0 x0 hx0)
      (((trivRep G ℤ).resSub U).coch.cls 2 _ hry)) =
      cupCoh bP 0 2 (M.coch.cls 0 (cor.f 0 x0) hcx) ((trivRep G ℤ).coch.cls 2 y hy) :=
    cupCor_holds ℤ G M (trivRep G ℤ) M U bP bU (cupCoh bP) (cupCoh bU) cor cor hU rfl (cupCoh_isCup bP)
      (cupCoh_isCup bU) hcor hcor 0 2 ((M.resSub U).coch.cls 0 x0 hx0) ((trivRep G ℤ).coch.cls 2 y hy)
  obtain ⟨zU', hzU', hzU1', hzU2'⟩ := cupCoh_isCup bU 0 2 x0 _ hx0 hry
  obtain ⟨w, hw, hw1, hw2⟩ := cupCoh_isCup bP 0 2 (cor.f 0 x0) y hcx hy
  rw [hzU2', hw2] at key
  have e1 : zU' = zU := by
    refine Subtype.ext (funext fun g => ?_)
    rw [hzU1', cupFun_zero_two]
    exact (smulPairing_apply M x _).trans (hzU1 g).symm
  have e2 : w = z := by
    refine Subtype.ext (funext fun g => ?_)
    rw [hw1, cupFun_zero_two, hcor, hx']
    exact (smulPairing_apply M x' _).trans (hz1 g).symm
  subst e1 e2
  exact key

end general

theorem corFun_zero_eq_normHom (hL : FiniteDimensional ℚ_[p] L) (y : KbarMult p) (hy : y ∈ multOf p L)
    (f : (Fin 0 → subG p K L) → (kbarT p K).V) (hf : ∀ g, f g = y) (g : Fin 0 → GK p K) :
    corFun (kbarT p K) (subG p K L) 0 f g = normHom p K L y := by
  have := finite_GalLK (p := p) (K := K) hL
  have := Fintype.ofFinite (GK p K ⧸ subG p K L)
  rw [normHom_apply, ← finsum_eq_sum_of_fintype,
    ← finsum_comp_equiv (QuotientGroup.quotientRightRelEquivQuotientLeftRel (subG p K L))]
  unfold corFun
  simp only [hf]
  refine finsum_congr fun c => ?_
  have h1 : QuotientGroup.quotientRightRelEquivQuotientLeftRel (subG p K L) c =
      (QuotientGroup.mk (c.out⁻¹) : GK p K ⧸ subG p K L) := by
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  rw [h1, kbarRep_out y hy]
  rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField
