import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiextensionTrivialOfTranslateDifferenceTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtHeckePointWeilPairingOrthogonalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HeckeFibre

theorem transl_triv {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (M : LB A.left) (hM : M.IsLB) (hR : Out.Rigidified A M) (K : Type) [Field K] [IsAlgClosed K]
    (y : Sp K ⟶ S) (n : ℕ) (hn : (n : K) ≠ 0) (x : Over.mk y ⟶ A) (hx : x ^ n = 1)
    (h : ∀ z : Over.mk y ⟶ A, z ^ n = 1 → Out.WeilIs A M (n : ℤ) x z 1) :
    ∃ t : (Out.translDiff A M x).Gen, t.IsGen := by
  obtain ⟨L, hL, ⟨c⟩⟩ := GlobalTheory.Moduli.cubicalStr_of_triv_theta GlobalTheory.abelianSchemeLaws_all.1 _ A hA M hM hR
    (GlobalTheory.WeilIntegral.triv_theta GlobalTheory.CubeTop.cubeTheorem hA hM)
  subst hL
  exact GlobalTheory.OrthKer.mem_kernel_of_cubWeil_orthogonal K S y A hA L c n hn x hx
    (fun z hz => (GlobalTheory.UU.cubWeil_iff_weilIs GlobalTheory.globalFns_holds hA hx hz 1).2 (h z hz))

theorem pic_field_eq_zero (K : Type) [Field K] (c : GlobalTheory.CechPic.Pic (Sp K)) : c = 0 := by
  obtain ⟨V, hV, hc⟩ := GlobalTheory.AbDual.exists_pull_eq_zero c (IsLocalRing.closedPoint K)
  have h := GlobalTheory.AbDual.pull_eq_zero_of_mem V (𝟙 _) (fun z => by
    have : z = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact hV) hc
  rwa [GlobalTheory.CechPic.pull_id] at h

theorem rigidified_diag {S : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB)
    (rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) :
    Out.Rigidified A (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
  have h0 := (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 rig₁
  refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB (pull_isLB hP _) _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull (pull_isLB hP _), GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp]
  have e : eSec A ≫ (lift (𝟙 A) (𝟙 A)).left = eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
    have h1 : η[A] ≫ (1 : A ⟶ A) = η[A] := by
      rw [MonObj.comp_one, CategoryTheory.Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    simp only [eSec, ← Over.comp_left, comp_lift, Category.comp_id, h1]
  rw [e, GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hP _ (pull_isLB hP _), h0, map_zero]

end GlobalTheory.HeckeFibre

namespace GlobalTheory.HeckeFibre

theorem fibre_triv : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).pull (pullback.fst o.A.hom y)).Gen, t.IsGen := by
  intro p _ D R _ b g c k N hc hk hN3 hNp hEF hsurj hdvd S s o h hh K _ _ y
  obtain ⟨x, rfl⟩ := hh
  obtain ⟨β, hβ⟩ : ∃ β : R →+* K, y ≫ s = spMap β :=
    ⟨(Spec.preimage (y ≫ s)).hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := o.geom K y β hβ
  obtain ⟨n, h', hn0, hnp, hsq, hpow, hW⟩ :=
    GlobalTheory.T.exists_sqrt_heckePoint_weilPairing_orthogonal D K _ _ _ I g c k N hc hk (by omega) hNp hEF hsurj hdvd x
  have hnK : (n : K) ≠ 0 := by
    have := (b.unit n hnp).map β
    rw [map_natCast] at this
    exact this.ne_zero
  have htr := transl_triv o.A o.ab _ (pull_isLB o.isLB _) (rigidified_diag o.A o.P o.isLB o.rig₁) K y n hnK
    (h' ^ (k ^ 2 / c)) hpow (fun z hz => by
      have w := hW z hz
      have e1 : unitOn (1 : Kˣ) = 1 := map_one _
      rw [e1] at w
      exact w)
  exact GlobalTheory.T.biextension_trivial_of_translate_difference_trivial o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm (Over.mk y) (pic_field_eq_zero K)
    (o.eta (N • g x)) h' (k ^ 2 / c) (by rw [hsq, hI]) htr

end GlobalTheory.HeckeFibre
