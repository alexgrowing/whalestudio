import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleBaseChangeIsoSemiabelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubWeilOneOfTrivPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelOfCubWeilOrthogonal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilKernel

theorem triv_slice_of_forall_weilIs_one : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), (n : k) ≠ 0 → ∀ a : Over.mk x ⟶ A, a ^ n = 1 → (∀ b : Over.mk x ⟶ A, b ^ n = 1 → Out.WeilIs (G2 A) P (n : ℤ) (lift a 1) (lift 1 b) 1) → (∃ t : (P.pull (lift (snd A (Over.mk x) ≫ a) (fst A (Over.mk x))).left).Gen, t.IsGen) := by
  intro S A _ _ P hA hL h1 h2 k _ _ p n hn a ha hpair
  have hB : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have ht2 : Triv (AbDual.ev P (𝟙 A) (1 : A ⟶ A)) := h2
  obtain ⟨r, hr⟩ : Triv (P.pull (eSec (A ⊗ A))) := by
    have e := (AbDual.triv_ev_iff hL _ _).2 (AbDual.evc_one_right hL ht2 (1 : 𝟙_ (Over S) ⟶ A))
    have e' : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = η[A ⊗ A] := by
      ext <;> simp [Hom.one_def]
    rw [AbDual.ev, e'] at e
    exact e
  obtain ⟨t, ht⟩ := WeilIntegral.triv_theta CubeTop.cubeTheorem hB hL
  obtain ⟨t', ht', hn'⟩ := AbLaw.Cube.exists_normalised hL t ht
  let M : RigLB (A ⊗ A) := ⟨P, r, hL, hr⟩
  have c : CubicalStr (A ⊗ A) M := AbLaw.Cube.cubicalOfNormalised globalFns_holds hB M t' ht' hn'
  have ha' : (lift a (1 : Over.mk p ⟶ A)) ^ n = 1 := WeilIntegral.lift_pow ha (one_pow n)

  have s1 : ∀ b : Over.mk p ⟶ A, b ^ n = 1 → CubWeil c n (lift a 1) (lift 1 b) 1 := fun b hb =>
    (cubWeil_iff_weilIs (c := c) globalFns_holds hB ha' (WeilIntegral.lift_pow (one_pow n) hb) 1).2 (hpair b hb)

  have s2 : ∀ b : Over.mk p ⟶ A, b ^ n = 1 → CubWeil c n (lift b 1) (lift a 1) 1 := by
    intro b hb
    have h := RaynaudAxis.cubWeil_one_of_triv_pull S (A ⊗ A) A (lift (𝟙 A) 1) hA inferInstance M c h2 n
      (Over.mk p) b a hb ha
    simpa using h

  have s3 : ∀ z : Over.mk p ⟶ A ⊗ A, z ^ n = 1 → CubWeil c n (lift a 1) z 1 := by
    intro z hz
    have e : lift (z ≫ fst A A) 1 * lift 1 (z ≫ snd A A) = z := by
      ext <;> simp [MonObj.mul_comp]
    have hz1 : (z ≫ fst A A) ^ n = 1 := by rw [← MonObj.pow_comp, hz]; simp
    have hz2 : (z ≫ snd A A) ^ n = 1 := by rw [← MonObj.pow_comp, hz]; simp
    have h := ((s2 _ hz1).mul_left (s1 _ hz2).symm).symm
    rw [e] at h
    simpa using h

  have ht := OrthKer.mem_kernel_of_cubWeil_orthogonal k S p (A ⊗ A) hB M c n hn (lift a 1) ha' s3
  have hD : (translDiff (A ⊗ A) P (lift a 1)).IsLB := LB.isLB_linComb hL _ _
  have h0 : CechPic.cls _ hD = 0 := (CechPic.cls_eq_zero_iff hD).2 ht

  have e := AbDual.pull_translDiff hL (lift a 1) hD (snd A (Over.mk p)) (lift 1 (fst A (Over.mk p)))
  rw [h0, map_zero] at e
  have k1 : (snd A (Over.mk p) ≫ lift a 1) * lift 1 (fst A (Over.mk p)) =
      lift (snd A (Over.mk p) ≫ a) (fst A (Over.mk p)) := by
    ext <;> simp [MonObj.mul_comp]
  have k2 : CechPic.pull (lift (1 : A ⊗ Over.mk p ⟶ A) (fst A (Over.mk p))).left (CechPic.cls P hL) = 0 := by
    have e1 : AbDual.evc hL (1 : A ⟶ A) (𝟙 A) = 0 := (AbDual.triv_ev_iff hL _ _).1 h1
    have e2 : lift (1 : A ⊗ Over.mk p ⟶ A) (fst A (Over.mk p)) =
        fst A (Over.mk p) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
      ext <;> simp
    have e3 : CechPic.pull (lift (1 : A ⟶ A) (𝟙 A)).left (CechPic.cls P hL) = 0 := e1
    rw [e2, Over.comp_left, CechPic.pull_comp, e3, map_zero]
  rw [k1, k2, sub_zero] at e
  exact (AbDual.triv_ev_iff hL _ _).2 e.symm

end GlobalTheory.WeilKernel
