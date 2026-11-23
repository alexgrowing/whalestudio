import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleLengthCompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentKernelEqCokerOmegaMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueKernelOrderPPowerDegreeIsogenyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasKernelOrderPPowerDegreeCompLeAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupIsogenyBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoIsogenyOmegaAndDualSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupExistsFactorThroughIsogenyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientKernelSupFrobeniusKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsogenyHeightEqDualSameDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientPDivGroupClosedSubgroupPTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColengthOfHeightOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenousPDivGroupFinrankOmegaDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorPropertiesStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.ColengthDegree

variable {p : ℕ} [Fact p.Prime] (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem map_comp {X Y Z : PDivGroup p k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    T.map (f ≫ g) = T.map f ∘ₗ T.map g :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k X Y Z trivial trivial trivial).2.1 f g

theorem map_id (X : PDivGroup p k) : T.map (𝟙 X) = LinearMap.id :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k X X X trivial trivial trivial).1

theorem map_iso_bijective {X Y : PDivGroup p k} (i : X ≅ Y) : Function.Bijective (T.map i.hom) := by
  have e₁ : T.map i.inv ∘ₗ T.map i.hom = LinearMap.id := by rw [← map_comp, i.inv_hom_id, map_id]
  constructor
  · exact Function.LeftInverse.injective (g := T.map i.inv) fun a => congrArg (fun g => g a) e₁
  · intro a
    refine ⟨T.map i.inv a, ?_⟩
    have e : T.map i.hom ∘ₗ T.map i.inv = LinearMap.id := by rw [← map_comp, i.hom_inv_id, map_id]
    exact congrArg (fun g => g a) e

theorem colen_comp {X Y Z : PDivGroup p k} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : Function.Injective (T.map f)) :
    Module.length (WittVector p k) (T.M X ⧸ LinearMap.range (T.map (f ≫ g))) =
      Module.length (WittVector p k) (T.M X ⧸ LinearMap.range (T.map f)) +
        Module.length (WittVector p k) (T.M Y ⧸ LinearMap.range (T.map g)) := by
  rw [map_comp]
  exact (GlobalTheory.T.witt_module_length_composition p k (T.M X) (T.M Y) (T.M Z)).1 _ _ hf

theorem colen_iso {X Y : PDivGroup p k} (i : X ≅ Y) :
    Module.length (WittVector p k) (T.M X ⧸ LinearMap.range (T.map i.hom)) = 0 := by
  rw [LinearMap.range_eq_top.2 (map_iso_bijective T i).2]
  exact Module.length_eq_zero_iff.2 inferInstance

omit [PerfectRing k p] in

theorem omegaMap_surjective_of_isIso {X Y : PDivGroup p k} (f : X ⟶ Y) [IsIso f] :
    Function.Surjective (omegaMap X Y f) := by
  intro w
  refine ⟨omegaMap Y X (inv f) w, ?_⟩
  rw [← LinearMap.comp_apply, ← omegaMap_comp, IsIso.hom_inv_id, omegaMap_id, LinearMap.id_apply]

omit [PerfectRing k p] in

theorem exists_step {X Y : PDivGroup p k} (f : X ⟶ Y) (hω : ¬ Function.Surjective (omegaMap X Y f)) :
    ∃ (Q : PDivGroup p k) (q₁ : X ⟶ Q) (q₁' : Q ⟶ X) (r : Q ⟶ Y),
      q₁ ≫ q₁' = (p : ℤ_[p]) • 𝟙 X ∧ q₁' ≫ q₁ = (p : ℤ_[p]) • 𝟙 Q ∧
      frobKerIdeal p k (X.A 1) ≤ kerIdeal (q₁.app 1) ∧ q₁ ≫ r = f ∧
      ¬ Function.Surjective (omegaMap X Q q₁) := by
  obtain ⟨C, _, _, _, _, π, hπs, hker, -, hfrob⟩ := GlobalTheory.T.exists_quotient_kernel_sup_frobeniusKernel p k X Y f
  obtain ⟨Q, q₁, q₁', h1, h2, hk1⟩ := GlobalTheory.T.exists_quotient_pDivGroup_closedSubgroup_pTorsion p k X C π hπs
  have hle : kerIdeal (f.app 1) ≤ kerIdeal (q₁.app 1) := by rw [hk1, hker]; exact le_sup_left
  obtain ⟨r, hr⟩ := GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny p k X Q Y 1 q₁ q₁' f (by rw [pow_one]; exact h1)
    (by rw [pow_one]; exact h2) hle
  refine ⟨Q, q₁, q₁', r, h1, h2, by rw [hk1, hker]; exact le_sup_right, hr, ?_⟩
  intro hs
  apply hω
  have e1 := (GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k X Q q₁ C π hπs).2.1 (by rw [hk1]; exact le_sup_left) (by rw [hk1])
  have e2 := (GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k X Y f C π hπs).2.1 (by rw [hker]; exact sup_le_sup_left hfrob _)
    (by rw [hker]; exact le_sup_left)
  haveI := finite_omega_of_eq_zero (CharP.cast_eq_zero k p) X
  have h0 : Module.finrank k (X.omega ⧸ LinearMap.range (omegaMap X Q q₁)) = 0 := by
    rw [LinearMap.range_eq_top.2 hs]
    exact Module.finrank_zero_of_subsingleton
  rw [e1, ← e2] at h0
  have hsub := Module.finrank_zero_iff.1 h0
  rw [← LinearMap.range_eq_top, eq_top_iff]
  intro x _
  exact (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)

omit [PerfectRing k p] in

theorem one_le_deg {X Q : PDivGroup p k} (q₁ : X ⟶ Q) (q₁' : Q ⟶ X)
    (h1 : q₁ ≫ q₁' = (p : ℤ_[p]) • 𝟙 X) (h2 : q₁' ≫ q₁ = (p : ℤ_[p]) • 𝟙 Q)
    (hns : ¬ Function.Surjective (omegaMap X Q q₁)) (e₁ : ℕ) (he₁ : HasLogDeg q₁ e₁) : 1 ≤ e₁ := by
  rcases Nat.eq_zero_or_pos e₁ with h | h
  · subst h
    have hI : IsIsog q₁ := ⟨1, q₁', by rw [pow_one]; exact h1, by rw [pow_one]; exact h2⟩
    haveI := ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k X).2.2.2 Q q₁ hI).1 he₁
    exact absurd (omegaMap_surjective_of_isIso q₁) hns
  · exact h

theorem kernelDegree_le_dieudonneColength_of_colength_eq (n : ℕ) : ∀ (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e →
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = n → e ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G H q e hq he hn
  by_cases hA : Function.Surjective (omegaMap G H q)
  · by_cases hB : Function.Surjective (omegaMap H.dual G.dual (dualHom G H q))
    · haveI := GlobalTheory.T.isIso_isogeny_omega_and_dual_surjective p k G H q hq hA hB
      have h0 : HasLogDeg q 0 := ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).2.2.2 H q hq).2 inferInstance
      have := (GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k G H q hq).unique he h0
      omega
    · obtain ⟨Q, q₁, q₁', r, h1, h2, hfr, hr, hns⟩ := exists_step (dualHom G H q) hB
      have hg := GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree p k G H q hq
      have hq₁ : IsIsog q₁ := ⟨1, q₁', by rw [pow_one]; exact h1, by rw [pow_one]; exact h2⟩
      have hrI : IsIsog r := (GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k H.dual).2.2.1 Q G.dual q₁ r hq₁ (hr ▸ hg.2.1)
      obtain ⟨e₁, he₁⟩ := (GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k H.dual Q q₁ hq₁).exists
      obtain ⟨e₂, he₂⟩ := (GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k Q G.dual r hrI).exists
      have hle : e ≤ e₁ + e₂ :=
        GlobalTheory.T.hasKernelOrderPPowerDegree_comp_le_add p k H.dual Q G.dual q₁ r e₁ e₂ e he₁ he₂ (hr ▸ hg.2.2 e he)
      have h1e := one_le_deg q₁ q₁' h1 h2 hns e₁ he₁
      have hL1 := (GlobalTheory.T.kernelDegree_le_dieudonneColength_of_heightOne p T k H.dual Q q₁ q₁' e₁ h1 h2 hfr he₁).2.1
      have hgr := GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree p k Q G.dual r hrI
      have hg₁ := GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree p k H.dual Q q₁ hq₁
      have hcomp : dualHom _ _ (dualHom G H q) = dualHom Q G.dual r ≫ dualHom H.dual Q q₁ := by
        rw [← hr]; rfl
      have hlen : Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) =
          Module.length (WittVector p k)
              (T.M G.dual.dual ⧸ LinearMap.range (T.map (dualHom Q G.dual r))) +
            Module.length (WittVector p k)
              (T.M Q.dual ⧸ LinearMap.range (T.map (dualHom H.dual Q q₁))) := by
        have a1 := colen_comp T G.bidual.hom (dualHom _ _ (dualHom G H q)) (map_iso_bijective T _).1
        have a2 := colen_comp T q H.bidual.hom (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G H q hq).1
        rw [bidual_hom_dualHom_dualHom q, a2] at a1
        simp only [colen_iso, add_zero, zero_add] at a1
        rw [a1, hcomp, colen_comp T _ _ (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k _ _ _ hgr.2.1).1]
      obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k _ _ _ hgr.2.1).2.1
      obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k _ _ _ hg₁.2.1).2.1
      rw [← ha, ← hb] at hlen
      rw [← hb] at hL1
      rw [hlen] at hn
      have hab : a + b = n := by exact_mod_cast hn
      have hbe : e₁ ≤ b := by exact_mod_cast hL1
      have := ih a (by omega) _ _ (dualHom Q G.dual r) e₂ hgr.2.1 (hgr.2.2 e₂ he₂) ha.symm
      omega
  · obtain ⟨Q, q₁, q₁', r, h1, h2, hfr, hr, hns⟩ := exists_step q hA
    have hq₁ : IsIsog q₁ := ⟨1, q₁', by rw [pow_one]; exact h1, by rw [pow_one]; exact h2⟩
    have hrI : IsIsog r := (GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).2.2.1 Q H q₁ r hq₁ (hr ▸ hq)
    obtain ⟨e₁, he₁⟩ := (GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k G Q q₁ hq₁).exists
    obtain ⟨e₂, he₂⟩ := (GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k Q H r hrI).exists
    have hle : e ≤ e₁ + e₂ := GlobalTheory.T.hasKernelOrderPPowerDegree_comp_le_add p k G Q H q₁ r e₁ e₂ e he₁ he₂ (hr ▸ he)
    have h1e := one_le_deg q₁ q₁' h1 h2 hns e₁ he₁
    have hL1 := (GlobalTheory.T.kernelDegree_le_dieudonneColength_of_heightOne p T k G Q q₁ q₁' e₁ h1 h2 hfr he₁).1
    have hlen := colen_comp T q₁ r (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G Q q₁ hq₁).1
    rw [hr] at hlen
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G Q q₁ hq₁).2.1
    obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k Q H r hrI).2.1
    rw [← ha, ← hb] at hlen
    rw [← ha] at hL1
    rw [hlen] at hn
    have hab : a + b = n := by exact_mod_cast hn
    have hae : e₁ ≤ a := by exact_mod_cast hL1
    have := ih b (by omega) _ _ r e₂ hrI he₂ hb.symm
    omega

end GlobalTheory.Dieu.ColengthDegree

namespace GlobalTheory.Dieu

theorem le_length_coker_of_hasLogDeg : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e →
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) := by
  intro p _ T k _ _ _ G H q e hq he
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G H q hq).2.1
  rw [← hn]
  exact_mod_cast ColengthDegree.kernelDegree_le_dieudonneColength_of_colength_eq T n G H q e hq he hn.symm

end GlobalTheory.Dieu
