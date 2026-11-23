import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

theorem exists_evalPt_injective {X : Scheme.{0}} [IsIntegral X] (V : X.Opens) (hV : (V : Set X).Nonempty) :
    ∃ (K : Type) (_ : Field K) (y : Sp K ⟶ X) (_ : ⊤ ≤ y ⁻¹ᵁ V),
      ∀ (V' : X.Opens) (_ : V ≤ V') (h' : ⊤ ≤ y ⁻¹ᵁ V'), Function.Injective (TangentOrigin.evalPt y V' h') := by
  obtain ⟨p, hp⟩ := hV
  obtain ⟨U₀, hU₀, hpU, hle⟩ := exists_isAffineOpen_mem_and_subset hp
  have hle' : U₀ ≤ V := hle
  haveI : Nonempty U₀ := ⟨⟨p, hpU⟩⟩
  obtain ⟨y, hy, e⟩ := TangentOrigin.exists_evalPt_eq hU₀ (algebraMap Γ(X, U₀) (FractionRing Γ(X, U₀)))
  refine ⟨FractionRing Γ(X, U₀), inferInstance, y, hy.trans (y.preimage_mono hle'), fun V' hV' h' a b hab => ?_⟩
  rw [← TangentOrigin.evalPt_res y (hle'.trans hV') h' hy, ← TangentOrigin.evalPt_res y (hle'.trans hV') h' hy,
    e] at hab
  exact map_injective_of_isIntegral X (homOfLE (hle'.trans hV')) (IsFractionRing.injective _ _ hab)

theorem exists_extend_of_charZero {F K : Type} [Field F] [NumberField F] [Field K] [CharZero K] (b : 𝓞 F →+* K) :
    ∃ ψ : F →+* K, ψ.comp (algebraMap (𝓞 F) F) = b := by
  have hb : Function.Injective b := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  exact ⟨IsFractionRing.lift hb, RingHom.ext fun a => IsFractionRing.lift_algebraMap hb a⟩

theorem exists_generic_evalPt_injective {F : Type} [Field F] [NumberField F] {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)}
    {jB : W ⟶ X} {s : W ⟶ Sp F} {d : ℕ} (hq : IsArithVar q d)
    (hW : IsPullback jB s q (spMap (algebraMap (𝓞 F) F))) (V : X.Opens) (hV : (V : Set X).Nonempty) :
    ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ W) (ψ : F →+* K) (_ : x ≫ s = spMap ψ) (h : ⊤ ≤ (x ≫ jB) ⁻¹ᵁ V),
      Function.Injective (TangentOrigin.evalPt (x ≫ jB) V h) := by
  haveI := hq.isIntegral
  obtain ⟨K, _, y, hy, hinj⟩ := exists_evalPt_injective V hV
  haveI : CharZero Γ(X, ⊤) := hq.charZero
  haveI : CharZero K := charZero_of_injective_ringHom (hinj ⊤ le_top le_rfl)
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 F →+* K, spMap b = y ≫ q := ⟨(Spec.preimage (y ≫ q)).hom, Spec.map_preimage _⟩
  obtain ⟨ψ, hψ⟩ := exists_extend_of_charZero b
  have w : y ≫ q = spMap ψ ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [← hb, ← hψ, ← Spec.map_comp]; rfl
  obtain ⟨x, hx₁, hx₂⟩ : ∃ x : Sp K ⟶ W, x ≫ jB = y ∧ x ≫ s = spMap ψ :=
    ⟨hW.lift y (spMap ψ) w, hW.lift_fst _ _ _, hW.lift_snd _ _ _⟩
  subst hx₁
  exact ⟨K, inferInstance, x, ψ, hx₂, hy, hinj V le_rfl hy⟩

theorem sum_smul_chain {K M : Type} [CommRing K] [AddCommMonoid M] [Module K M] {r : ℕ} {u v : Fin r → M} {w : M}
    (A : Matrix (Fin r) (Fin r) K) (b : Fin r → K) (h1 : ∀ i, v i = ∑ a, A a i • u a) (h2 : w = ∑ i, b i • v i) :
    w = ∑ a, (∑ i, A a i * b i) • u a := by
  simp only [h2, h1, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

attribute [local instance] Over.cartesianMonoidalCategory in
open MonoidalCategory CartesianMonoidalCategory MonObj in

theorem isCombAtG_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {T : Scheme.{0}} (t : SAB H T) {K : Type} [CommRing K] (x : Sp K ⟶ T) {r : ℕ}
    {u v : Fin r → (Sp (DualNumber K) ⟶ t.G.left)} {w : Sp (DualNumber K) ⟶ t.G.left}
    (hu : ∀ i, IsTanAtG t x (u i)) (hv : ∀ i, IsTanAtG t x (v i)) (hw : IsTanAtG t x w)
    (A : Matrix (Fin r) (Fin r) K) (b : Fin r → K) (hA : ∀ i, IsCombAtG t x u (fun a => A a i) (v i))
    (hb : IsCombAtG t x v b w) : IsCombAtG t x u (fun a => ∑ i, A a i * b i) w := by
  have h1 := fun i => (LieMet.isComb_iff (fun a => LieMet.tanOf (hu a)) _ (LieMet.tanOf (hv i))).1 (hA i)
  have h2 := (LieMet.isComb_iff (fun a => LieMet.tanOf (hv a)) _ (LieMet.tanOf hw)).1 hb
  refine (LieMet.isComb_iff (fun a => LieMet.tanOf (hu a)) _ (LieMet.tanOf hw)).2 ?_
  exact sum_smul_chain (M := ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G) (u := fun a => LieMet.tanOf (hu a))
    (v := fun a => LieMet.tanOf (hv a)) A b h1 h2

theorem isTrans_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (X W : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X) (πB : W ⟶ gen Z) (d : ℕ), IsArithVar q d → IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) → ∀ (r : ℕ) (τ : E →+* ℂ) (ι : Type) (U : ι → X.Opens) (u : ∀ i, LocAssign Z r jB (U i)) (A : ∀ i j, Matrix (Fin r) (Fin r) Γ(X, U i ⊓ U j)), (∀ i, IsLocFrame Z e jB πB r τ (U i) (u i)) → (∀ i j, IsTrans Z jB πB (u i) (u j) (A i j)) → (∀ i, A i i = 1) ∧ ∀ (i j k : ι) (V : X.Opens) (hij : V ≤ U i ⊓ U j) (hjk : V ≤ U j ⊓ U k) (hik : V ≤ U i ⊓ U k), (A i j).map (resG X hij) * (A j k).map (resG X hjk) = (A i k).map (resG X hik) := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W q jB πB d hq hW r τ ι U u A hu hA
  have key : ∀ (i j k : ι) (V : X.Opens) (hij : V ≤ U i ⊓ U j) (hjk : V ≤ U j ⊓ U k) (hik : V ≤ U i ⊓ U k),
      (A i j).map (resG X hij) * (A j k).map (resG X hjk) = (A i k).map (resG X hik) ∧
        (∀ hii : V ≤ U i ⊓ U i, (A i i).map (resG X hii) = 1) := by
    intro i j k V hij hjk hik
    rcases (V : Set X).eq_empty_or_nonempty with hV | hV
    · have hb : V = ⊥ := TopologicalSpace.Opens.coe_eq_empty.1 hV
      haveI : Subsingleton Γ(X, V) := CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hb)
      exact ⟨Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
    obtain ⟨K, _, x, ψ, hψ, h, hinj⟩ := exists_generic_evalPt_injective hq hW V hV
    have hm : ∀ {V' : X.Opens}, V ≤ V' → ⊤ ≤ (x ≫ jB) ⁻¹ᵁ V' := fun hV' => h.trans ((x ≫ jB).preimage_mono hV')
    have hi := hm (hij.trans inf_le_left)
    have hj := hm (hij.trans inf_le_right)
    have hk := hm (hjk.trans inf_le_right)
    have bi := (hu i).1 K x hi ψ hψ
    have bj := (hu j).1 K x hj ψ hψ
    have bk := (hu k).1 K x hk ψ hψ
    refine ⟨Matrix.ext fun a b => hinj ?_, fun hii => Matrix.ext fun a b => hinj ?_⟩
    · have h1 := isCombAtG_mul Z.t _ (fun a => (bi.1 a).1) (fun a => (bj.1 a).1) (bk.1 b).1
        ((A i j).map (TangentOrigin.evalPt (x ≫ jB) _ (hm hij))) _ (hA i j K x hi hj (hm hij))
        (hA j k K x hj hk (hm hjk) b)
      have h2 := congrFun ((bi.2 _ (bk.1 b)).unique h1 (hA i k K x hi hk (hm hik) b)) a
      simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul] at h2 ⊢
      simp only [TangentOrigin.evalPt_res (x ≫ jB) hij (hm hij) h, TangentOrigin.evalPt_res (x ≫ jB) hjk (hm hjk) h,
        TangentOrigin.evalPt_res (x ≫ jB) hik (hm hik) h]
      exact h2
    · have h2 := congrFun ((bi.2 _ (bi.1 b)).unique (hA i i K x hi hi (hm hii) b)
        (isCombAtG_single Z.t _ (fun a => (bi.1 a).1) b)) a
      rw [Matrix.map_apply, TangentOrigin.evalPt_res (x ≫ jB) hii (hm hii) h, h2, Matrix.one_apply, Pi.single_apply]
      split_ifs <;> simp
  refine ⟨fun i => ?_, fun i j k V hij hjk hik => (key i j k V hij hjk hik).1⟩
  have h := (key i i i (U i ⊓ U i) le_rfl le_rfl le_rfl).2 le_rfl
  rw [← h]
  ext a b
  simp [resG]

end GlobalTheory.ArLieBase

end
