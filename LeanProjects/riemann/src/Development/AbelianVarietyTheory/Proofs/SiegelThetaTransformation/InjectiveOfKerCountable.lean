import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSymplecticCoordinatesOfIsPeriod
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ConstOfNormFactorUnitFr
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ComponentEqOfMatchedLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTestRingInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongrOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsUnf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsVal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem injective_of_ker_countable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (h : V →ₗ[ℂ] W) {S : Set V} (hS : S.Countable) (hk : ∀ v, h v = 0 → v ∈ S) : Function.Injective h := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hne
  have hi : Function.Injective fun t : ℂ => t • v := smul_left_injective ℂ hne
  have : (Set.univ : Set ℂ).Countable := (hS.preimage hi).mono fun t _ => hk _ (by rw [map_smul, hv, smul_zero])
  exact not_countable_complex this

open MonObj in

theorem exists_isometry [Algebra c.F ℂ] {r g g' : ℕ} {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}
    {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r} {L : Lt E r} {y : FrPt Xo c ℂ}
    (A : AnFib X bas idx e x L y) (hs : IsSympl X bas) (hx : x ∈ X.dom) (hg : g = g') {σ' : KA l →+* ℂ}
    {ty : Fin g' → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (i : Fin F.n) {P : (F.Di i).La →+ (Fin g' → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) (hy : y.x = F.u i P) :
    ∃ gam : L ≃ₗ[𝓞 E] (F.Di i).La, (∀ a b : L, (((F.Di i).EF (gam a) (gam b) : ℤ) : ℚ) = EF X a b) ∧
      ∀ (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)) (hm : ∀ a, mk a ∈ L), A.Marked mk →
        ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u, gam ⟨mk a, hm a⟩ = F.t i a + l.M • u := by
  obtain ⟨hconj, -, him, -, hsm, hinj, -⟩ := hx_laws E r X g bas idx 0 hs Even.zero x hx
  obtain ⟨y0, hy0, u, tan, eig, basis, s, gen⟩ := y
  change y0 = _ at hy
  subst hy
  obtain ⟨h, hh, -⟩ := HolHom.existsUnique_linear_ex F i hP (e := A.ex) A.ex_add A.hol
  have hadd : ∀ u v, pv X idx x (u + v) = pv X idx x u + pv X idx x v := fun u v => by
    unfold pv; rw [per_add]; rfl
  have hk : ∀ a : L, ∃ b, P b = h (pv X idx x a) := fun a =>
    (F.ex_ker i P hP _).1 ((hh _).symm.trans ((A.ex_ker _).2 ⟨a, a.2, rfl⟩))
  choose gam hgam using hk
  have hker : ∀ z b, h z = P b → ∃ v ∈ L, z = pv X idx x v := fun z b hz =>
    (A.ex_ker z).1 ((hh z).trans ((F.ex_ker i P hP _).2 ⟨b, hz.symm⟩))
  have hhi : Function.Injective h := by
    have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
    exact injective_of_ker_countable h (Set.countable_range (pv X idx x)) fun v hv => by
      obtain ⟨w, -, hw⟩ := hker v 0 (hv.trans (map_zero P).symm)
      exact ⟨w, hw.symm⟩
  have hhs : Function.Surjective h := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hg])).1 hhi
  let ρ : 𝓞 E → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun a =>
    LinearMap.pi fun k => rowType X (idx k) (a : E) • LinearMap.proj k
  have hlin : ∀ (a : 𝓞 E) v k, h (ρ a v) k = ty k (a : E) * h v k := fun a =>
    FibreExp.intertwines F i hP h a (ρ a) fun v => by
      rw [← hh, ← hh]; exact A.ex_lin a v
  let gam₁ : L →ₗ[𝓞 E] (F.Di i).La :=
    { toFun := gam
      map_add' := fun a b => hP.2.1 (by rw [map_add, hgam, hgam, hgam, ← map_add, ← hadd]; rfl)
      map_smul' := fun a b => hP.2.1 (funext fun k => by
        rw [RingHom.id_apply, hP.1, hgam, hgam, ← hlin]
        exact congrArg (fun z => h z k) (hsm a b)) }
  have hb : Function.Bijective gam₁ := by
    refine ⟨fun a b hab => Subtype.ext (hinj (hhi ?_)), fun b => ?_⟩
    · rw [← hgam, ← hgam]; exact congrArg P hab
    · obtain ⟨z, hz⟩ := hhs (P b)
      obtain ⟨v, hv, rfl⟩ := hker z b hz
      exact ⟨⟨v, hv⟩, hP.2.1 ((hgam ⟨v, hv⟩).trans hz)⟩
  refine ⟨LinearEquiv.ofBijective gam₁ hb, fun a b => ?_, fun mk hm hmk a ha => ?_⟩
  · let lin : L → (Fin g → ℂ) →ₗ[ℂ] ℂ := fun a =>
      { toFun := fun z => Real.pi * Dict.hx X bas idx x z (pv X idx x a)
        map_add' := fun z w => by simp only [Dict.hx, mulVec_add, add_dotProduct, mul_add]
        map_smul' := fun t z => by
          simp only [Dict.hx, mulVec_smul, smul_dotProduct, smul_eq_mul, RingHom.id_apply]; ring }
    have hl : ∀ v, (F.ex i P (h v)).left = (A.ex v).left := fun v => by rw [hh]
    have key := FibreExp.alternating_eq F i hP h (fun a : L => pv X idx x a) gam (fun a => (hgam a).symm)
      (fr := A.fr) lin (fun a => Complex.log (A.χ a) +
        Real.pi / 2 * Dict.hx X bas idx x (pv X idx x a) (pv X idx x a))
      (fun j => by simp only [hl]; exact A.fr_hol j) (fun j v => by rw [hl]; exact A.fr_ne j v)
      (fun j j' v => by rw [hl]; exact A.fr_g j j' v) (fun a j v hv => by
        rw [hl] at hv
        have h0 : A.χ a ≠ 0 := by rw [← norm_ne_zero_iff, A.χ_norm a a.2]; exact one_ne_zero
        rw [A.fr_per a a.2 j v hv, add_left_comm, Complex.exp_add (Complex.log _), Complex.exp_log h0]
        rfl) a b
    change (Real.pi : ℂ) * Dict.hx X bas idx x _ _ - Real.pi * Dict.hx X bas idx x _ _ = _ at key
    rw [hconj (pv X idx x a) (pv X idx x b), ← mul_sub, ← neg_sub, Complex.sub_conj, him] at key
    have : ((EF X a b : ℚ) : ℂ) = (((F.Di i).EF (gam a) (gam b) : ℤ) : ℂ) := by
      apply mul_left_cancel₀ (neg_ne_zero.2 Complex.two_pi_I_ne_zero)
      rw [← key]
      push_cast
      ring
    change (((F.Di i).EF (gam a) (gam b) : ℤ) : ℚ) = _
    exact_mod_cast this.symm
  · have hM : (l.M : ℂ) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
    have h1 : F.ex i P ((l.M : ℂ)⁻¹ • P (F.t i a)) = F.ex i P ((l.M : ℂ)⁻¹ • P (gam ⟨mk a, hm a⟩)) := by
      rw [← F.ex_eta i P hP a ha, hgam, ← map_smul, ← hh]
      refine (hmk a ha).trans (congrArg A.ex ?_)
      rw [hsm]
      funext j
      simp
    have h2 := F.ex_add i P hP ((l.M : ℂ)⁻¹ • P (F.t i a))
      ((l.M : ℂ)⁻¹ • P (gam ⟨mk a, hm a⟩) - (l.M : ℂ)⁻¹ • P (F.t i a))
    rw [add_sub_cancel, ← h1, left_eq_mul] at h2
    obtain ⟨w, hw⟩ := (F.ex_ker i P hP _).1 h2
    refine ⟨w, hP.2.1 ?_⟩
    change P (gam _) = _
    rw [map_add, map_nsmul, hw, ← Nat.cast_smul_eq_nsmul ℂ, ← smul_sub, smul_inv_smul₀ hM, add_sub_cancel]

theorem exists_const {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (W : UW U) {f : Rul Xo c}
    (hf : f ∈ sec Xo c 0 0) (h1 : ∀ y : FrPt Xo c (CAt σ), ‖Formalism.L2.PjFree.toC (evR Xo c f y)‖ = 1) :
    ∃ C : U.Comp → ℂ, ∀ y : FrPt Xo c (CAt σ), ∃ k P, IsPeriod (W.F.Di (W.ik k)) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P ∧
      y.x = W.F.u (W.ik k) P ∧ Formalism.L2.PjFree.toC (evR Xo c f y) = C k := by
  obtain ⟨-, -, honto, -, hsec, -⟩ := hU
  have hC : ∀ k, ∃ C : ℂ, ∀ x : (U.X k).dom, Formalism.L2.PjFree.toC (evR Xo c f (U.un k x)) = C := fun k => by
    have hr : ∀ x : (U.X k).dom, Formalism.L2.PjFree.rdU U f k x = Formalism.L2.PjFree.toC (evR Xo c f (U.un k x)) := fun x => dif_pos x.2
    obtain ⟨C, -, hC⟩ := const_of_norm_factor (FourierCoefficientDomain.isOpen_dom (U.X k))
      (GlobalTheory.frames_isConnected E r (U.X k)).isPreconnected (J := Unit) (fun _ => Formalism.L2.PjFree.rdU U f k) (fun _ _ => 1) 1 one_pos
      (fun _ => (hsec 0 0 ⟨fun _ => antitone_const, Even.zero⟩ f hf k).1) (fun _ => differentiableOn_const _)
      fun x hx => ⟨_, (hr ⟨x, hx⟩).symm ▸ h1 (U.un k ⟨x, hx⟩), fun _ => (mul_one _).symm⟩
    exact ⟨C, fun x => by rw [← hr, hC () x x.2, mul_one]⟩
  choose C hC using hC
  refine ⟨C, fun y => ?_⟩
  obtain ⟨k, x, t, hb⟩ := honto y
  obtain ⟨P, -, hP, hx, -⟩ := W.pt k x
  refine ⟨k, P, hP, hb.1.trans hx, ?_⟩
  have hT : ∀ y : FrPt Xo c (CAt σ), FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y :=
    fun y => by
      by_contra hn
      have h0 : evR Xo c f y = 0 := dif_neg hn
      have := h1 y
      rw [h0] at this
      exact zero_ne_one ((norm_zero (E := ℂ)).symm.trans this)
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hw := (GlobalTheory.borDesc_and_wtField E H Dw l Xo c).2 0 0 f hf ℂ t (U.un k x) y (hT _) (hT _) hb
  have h0 : wchar (S := ℂ) (ex Dw 0 0) t = 1 := Finset.prod_eq_one fun i _ => by cases i <;> exact pow_zero _
  rw [h0, one_mul] at hw
  exact hw.trans (hC k x)

theorem evR_eq_of_marked (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (hA : l.A = 1) {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0)
    (h1 : ∀ y : FrPt Xo c (CAt σ), ‖Formalism.L2.PjFree.toC (evR Xo c f y)‖ = 1) {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {L : Lt E r} (hr : 1 ≤ r)
    (hs : IsSympl X bas) {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hm : ∀ a, mk a ∈ L) :
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ x ∈ X.dom, ∀ x' ∈ X.dom, ∀ (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x' L y'),
      A.Marked mk → A'.Marked mk → evR Xo c f y = evR Xo c f y' := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  intro x hx x' hx' y y' A A' hk hk'
  have hD : 1 ≤ Dw.p + Dw.q := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨τ'⟩ : Nonempty X.Ψ := by
      by_cases h : τ ∈ X.Ψ
      · exact ⟨⟨τ, h⟩⟩
      · exact ⟨⟨_, not_not.1 (mt (X.cmType τ).2 h)⟩⟩
    obtain ⟨ρ, i⟩ := e (idx.symm (τ', ⟨0, hr⟩))
    have := i.pos
    unfold Datum.mult at this
    split_ifs at this <;> omega
  obtain ⟨ξ₀, hcc, hne, him⟩ := GlobalTheory.IsUnfEx.exists_xi H
  have hcc' : FD.cc (-ξ₀) = -(-ξ₀) := by
    unfold FD.cc at hcc ⊢
    rw [map_neg, hcc]
  obtain ⟨Gm, φ, hφ⟩ :=
    GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne) (Dw.p + Dw.q) rfl
  obtain ⟨U, hU, -⟩ := GlobalTheory.FrameUnif.exists_unf_hasPrinc E H Dw l Xo c σ (Dw.p + Dw.q) ξ₀ Gm φ hD hσ hcc him hφ
  obtain ⟨W⟩ := nonempty_uw hU
  obtain ⟨C, hC⟩ := exists_const hU W hf h1
  obtain ⟨k, P, hP, hy, hv⟩ := hC y
  obtain ⟨k', P', hP', hy', hv'⟩ := hC y'
  have hg : g = W.g := Fin.equiv_iff_eq.1 ⟨e.trans W.e.symm⟩
  obtain ⟨ga, hE, hM⟩ := exists_isometry A hs hx hg W.F _ hP hy
  obtain ⟨ga', hE', hM'⟩ := exists_isometry A' hs hx' hg W.F _ hP' hy'
  obtain rfl : k = k' := by
    refine W.ik_injective hσ hU hD (index_eq_of_marked_isometry W.F hD hσ
      ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw W.g W.e) _ _ (ga.symm.trans ga') (fun a b => ?_) (fun a ha => ?_)
      fun a => ⟨ga' (ga.symm (W.F.t _ a)) - W.F.t _ a, by rw [hA, one_smul, add_sub_cancel]; rfl⟩)
    · have h := hE (ga.symm a) (ga.symm b)
      rw [ga.apply_symm_apply, ga.apply_symm_apply, ← hE'] at h
      exact_mod_cast h.symm
    · obtain ⟨u, hu⟩ := hM mk hm hk a ha
      obtain ⟨u', hu'⟩ := hM' mk hm hk' a ha
      refine ⟨u' - ga' (ga.symm u), ?_⟩
      rw [eq_sub_of_add_eq hu.symm, map_sub, map_nsmul, LinearEquiv.trans_apply, ga.symm_apply_apply, hu', smul_sub,
        add_sub_assoc]
      rfl
  exact hv.trans hv'.symm

theorem exists_cvIs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra d.c₂.F ℂ], GoodEmb d.c₂ (algebraMap d.c₂.F ℂ) → d.l₂.A = 1 → d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 → UnitC d → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (L : Lt E r), 1 ≤ r → IsSympl X bas → SelfD X L → ∃ cv : (Dw.La →ₗ[𝓞 E] (Fin r → E)) → ℂ, (∀ mk, ‖cv mk‖ = 1) ∧ CvIs d X bas idx e L cv := by
  intro E _ _ _ H Dw l Xo c n d inst hσ hA hf hu r g X bas idx e L hr hs _
  obtain ⟨σ, rfl⟩ : ∃ σ : d.c₂.F →+* ℂ, inst = σ.toAlgebra :=
    ⟨algebraMap d.c₂.F ℂ, Algebra.algebra_ext _ _ fun _ => rfl⟩
  letI : Algebra d.c₂.F ℂ := σ.toAlgebra
  have key : ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ x ∈ X.dom, ∀ (y : FrPt d.Xo₂ d.c₂ ℂ)
      (A : AnFib X bas idx e x L y), IsMark d.l₂ L mk → A.Marked mk → evR d.Xo₂ d.c₂ d.cδ y = v := fun mk => by
    by_cases h : ∃ x ∈ X.dom, ∃ (y : FrPt d.Xo₂ d.c₂ ℂ) (A : AnFib X bas idx e x L y), A.Marked mk
    · obtain ⟨x', hx', y', A', hk'⟩ := h
      exact ⟨_, hu _ y', fun x hx y A hm hk =>
        evR_eq_of_marked σ hσ hA hf (hu _) hr hs hm.mem x hx x' hx' y y' A A' hk hk'⟩
    · exact ⟨1, norm_one, fun x hx y A _ hk => absurd ⟨x, hx, y, A, hk⟩ h⟩
  choose cv h1 h2 using key
  exact ⟨cv, h1, fun x hx y A mk => h2 mk x hx y A⟩

end GlobalTheory.ClsVal
