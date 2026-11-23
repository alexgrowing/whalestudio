import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EmbeddingSectionsSpanGeometricFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjCoordRepresentationGeometricFibreSpanningStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsVeryAmpleSectionSystemOfProjectiveCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TwistedPowTranslate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.EmbVA

theorem act_unique (hL : Out.SymLiftSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) (k : ℕ) (z : ℤ)
    (hz : z = k) (ho : Odd k) (hu : IsUnit (k : Γ(S, ⊤))) {T : Over S} (x : T ⟶ P.A) (hx : x ^ k = 1)
    {θ θ' : Out.ThetaGrp P.A P.L z T} (h : Out.SymLift P.A P.L z k x θ) (h' : Out.SymLift P.A P.L z k x θ')
    {s s₁ s₂ : LB.Sec (Out.LPow P.A P.L z T)} (a₁ : Out.IsActOf P.A P.L z θ s s₁)
    (a₂ : Out.IsActOf P.A P.L z θ' s s₂) (j) : s₁.f j = s₂.f j := by
  subst hz
  have hc := (hL S P k ho hu T x hx).2 θ θ' h h'
  refine sec_ext_val P.isLB (s := s₁) (s' := s₂) (fun y J hJ => ?_) j
  have e₁ := GlobalTheory.ThetaPowOrder.act_sval a₁ (𝟙 _) y hJ
  have e₂ := GlobalTheory.ThetaPowOrder.act_sval a₂ (𝟙 _) y hJ
  have e₃ := val_corr hJ hc (𝟙 _)
  have e₄ : θ.pt = θ'.pt := h.pt_eq.trans h'.pt_eq.symm
  refine e₁.trans (Eq.trans ?_ e₂.symm)
  exact congrArg₂ (fun u (p : T ⟶ P.A) => Units.val u * sval (L := P.L) s (𝟙 _ ≫ (Out.translT P.A p).left) y J) e₃ e₄

theorem lbIso_pow {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (n : ℕ) (z : ℤ) (hz : z = n) :
    LBIso (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => z)) ((lbPow L n).pull f) := by
  subst hz
  refine LBIso.chartPull (h := f) (A := lbPow L n) (B := lbPow L n) ?_ (chartPullPull _ f f rfl)
    ⟨_, idIso_isGen (LB.isLB_linComb hL _ _)⟩
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => f) j ≤
      f ⁻¹ᵁ LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0
  refine ⟨fun j _ => j 0, le, fun y j j' hj hj' => ?_⟩
  refine (gm_linComb L _ _ (𝟙 Y) y j j' hj hj').trans (Eq.trans ?_
    (gm_linComb L (fun _ : PUnit => 𝟙 X) (fun _ => (n : ℤ)) f y _ _ (le j hj) (le j' hj')).symm)
  rw [Fin.prod_univ_one, Fintype.prod_unique, Category.id_comp, Category.comp_id]

theorem linComb_pow {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ} (y : Fin r → (T ⟶ A))
    (a : Fin r → ℕ) (n : ℕ) : Out.linComb y a ^ n = ∏ i, y i ^ (a i * n) := by
  rw [Out.linComb, List.prod_ofFn, ← Finset.prod_pow]
  simp only [pow_mul]

end GlobalTheory.EmbVA

namespace GlobalTheory

open EmbVA in

theorem embSec_veryAmple_periodic : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g (N' ^ 2) J b (spMap β)) (m : ℕ) σ, Odd N' → m ∣ N' → 2 ≤ m → t.Emb m (Over.mk (𝟙 (Sp K))) σ → IsIso (snd (Over.mk (𝟙 (Sp K))) t.A).left ∧ (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 (Sp K)))).IsLB ∧ VAmp (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ ∧ LBIso (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 (Sp K)))) ((lbPow t.L (m ^ 2)).pull (snd (Over.mk (𝟙 (Sp K))) t.A).left) ∧ (∀ a a' : Ix g (N' ^ 2), (∀ i, (a i).val ≡ (a' i).val [MOD m ^ 2]) → ∀ j, (σ a).f j = (σ a').f j) ∧ TorsBasis t.A (N' ^ 2) t.pt ∧ ∀ x : Out.baseOver (Sp K) ⟶ t.A, x ^ N' = 1 → ∃ h, t.lab h ^ N' = x := by
  intro hL hL2 o _ g N' J b K _ _ β t m σ hN hm h2 hE
  haveI := t.ab.comm
  have hN0 : N' ≠ 0 := by rintro rfl; simp at hN
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN0⟩
  have hid : (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) = 𝟙 _ := rfl
  have hbij : ∀ y : Out.baseOver (Sp K) ⟶ t.A, y ^ (N' ^ 2) = 1 →
      ∃! c : Fin (2 * g) → ZMod (N' ^ 2), Out.linComb t.pt (fun i => (c i).val) = y := fun y hy => by
    have := t.bij K (𝟙 _) y hy
    simpa only [hid, Category.id_comp] using this
  refine ⟨?_, LB.isLB_linComb t.isLB _ _, ?_, lbIso_pow t.isLB _ _ _ (by push_cast; rfl), ?_, ⟨Nat.pos_of_neZero _, t.torsion, hbij⟩, ?_⟩
  · show IsIso (pullback.snd (𝟙 (Sp K)) t.A.hom)
    infer_instance
  · refine GlobalTheory.T.isVeryAmpleSectionSystem_of_projectiveCoordinates K _ _ _ _ _ _ (GlobalTheory.T.projCoordRepresentation_geometric_fibre_spanning hL hL2 _ t.pol K (𝟙 _) _ _ σ (by nlinarith) ?_)
    exact GlobalTheory.EmbSpan.emb_span_eq_top hL hL2 o g N' J b _ _ t m K (𝟙 _) σ hN hm h2 hE
  · intro a a' haa j
    obtain ⟨th, s1, α, U, -, -, -, hU, hact⟩ := hE
    obtain ⟨c, rfl⟩ := hm
    have hm0 : 0 < m := by omega
    have hc : m * c / m = c := Nat.mul_div_cancel_left c hm0
    have hlab : t.lab a ^ (c ^ 2) = t.lab a' ^ (c ^ 2) := by
      rw [TObj.lab, TObj.lab, linComb_pow, linComb_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      refine pow_eq_pow_of_modEq ?_ (t.torsion i)
      exact ((haa i).mul_right' _).of_dvd (dvd_of_eq (mul_pow m c 2))
    have htor : (t.lab a ^ (c ^ 2)) ^ (m ^ 2) = 1 := by
      rw [← pow_mul, TObj.lab, linComb_pow]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [show (a i).val * (c ^ 2 * m ^ 2) = (m * c) ^ 2 * (a i).val by ring, pow_mul, t.torsion, one_pow]
    have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Sp K, ⊤)) := by
      have h1 := (b.unit.map β).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      rw [map_natCast, map_natCast, mul_pow, Nat.cast_mul] at h1
      exact isUnit_of_mul_isUnit_left h1
    have h₁ := hU a
    have h₂ := hU a'
    simp only [Over.mk_hom, hid, Category.id_comp, hc] at h₁ h₂
    rw [← hlab] at h₂
    exact act_unique hL.symLift t.pol (m ^ 2) _ (by push_cast; rfl) (Odd.of_dvd_nat hN (Dvd.intro c rfl)).pow hu _ htor
      h₁ h₂ (hact a) (hact a') j
  · intro x hx
    obtain ⟨h1, -, h3, -⟩ := hL.mulN _ t.pol N' (Nat.pos_of_ne_zero hN0)
    obtain ⟨d, hd⟩ := TwistTranslate.exists_root t.pol (𝟙 (Sp K)) N' x
    have hd' : (show Out.baseOver (Sp K) ⟶ t.A from d) ^ N' = x := hd
    obtain ⟨h, hh, -⟩ := hbij d ((congrArg (fun n => (show Out.baseOver (Sp K) ⟶ t.A from d) ^ n) (pow_two N')).trans (by rw [pow_mul, hd', hx]))
    exact ⟨h, (congrArg (· ^ N') hh).trans hd'⟩

end GlobalTheory
end
