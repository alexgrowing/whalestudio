import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrcSingleApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RdEmbEvz
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsBranchingMapEquivariantNonzeroCommon
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LamTEqLamTHcW
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotUnitRatioBase
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartIndexInjectiveOffLastStep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

open Formalism.L2.Col in

theorem tailTop_eq_of_pin : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → (∀ c, stabOrd UT (h c) = Nat.card ((I.fm l u a).stabilizer₂ c)) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ n (hn : n = (I.rec7 l Z).R.m), ∀ ψ ∈ k.Ram n, ∀ f : CXP R P t, (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * ∑ β ∈ @Finset.univ (k.Ch n) (k.fin n), ∑ c : (I.fm l u a).clsP, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f ((realOf u R g s J).low n hn fun z => k.rd n β ψ (((realOf u R g s J).fr n).symm z) ((g.oT n hn).emb (h c, 1))) = k.cP * (tupOf R P u g t r k tl).tail n hn ψ f := by
  intro B X I hI hP l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hRP heW hbT hLev hG h hh hst G' hG' n hn ψ hψ f
  subst hn
  have hC : PinColL A ι R.ψ R.θ g.x g.vac c₀ k.kom k.dd w k.Ram k.rd k.cK := hCh
  have hIs : A.Is := hC.is
  have hψF : ψ ∈ (I.fm l u a).Fi B.R.m := ((hC.ram B.R.m le_rfl ψ).1 hψ).1.1
  have hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1 := N_m_succ B.R

  obtain ⟨Lz, hLz⟩ : ∃ Lz, Lz = (I.per l u a).lowerMap ((I.per l u a).evz ψ) := ⟨_, rfl⟩
  have hlow : ∀ c (y : FrN (I.rec7 l Z) (B.R.N B.R.m - 1)),
      Lz c ⟨y.1, y.2⟩ = lowOf I l Z u (fun y' => (I.per l u a).evz ψ c ⟨y'.1, y'.2⟩) y :=
    fun c y => hLz ▸ (GlobalTheory.TrueBranch.branching_true_columns I hI hP l Z u hN).2.2.2 a _ c y
  have heL : ∀ c, eW Lz c = fun y => lowOf I l Z u (fun y' => (I.per l u a).evz ψ c ⟨y'.1, y'.2⟩) ⟨y.1, y.2⟩ := by
    intro c; funext y
    rw [heW Lz c y ⟨y.1, y.2⟩ rfl]
    exact hlow c ⟨y.1, y.2⟩

  have hw : ∀ c, eW Lz c ∈ LinearMap.range j := by
    intro c
    rw [hj.range]
    have hv0 := GlobalTheory.EvzVal.evz_mem_valC I hI hP l Z u a ψ hψF c
    have hv1 := (GlobalTheory.TrueBranch.branching_true_columns I hI hP l Z u hN).2.1.1 _ hv0
    obtain ⟨Pp, hPp, hEq⟩ := hv1
    rw [heL c]
    exact ⟨Pp, hPp, funext fun y => congrFun hEq ⟨y.1, y.2⟩⟩
  obtain ⟨G'', hR'', htl⟩ := hG ψ f
  have hper : (I.per l u a).Ptil ψ (G' f) = tl ψ f := by
    rw [htl]
    have := GlobalTheory.Fam.Check.ReadsG.period_eq K eW j g.bT (hG' f) hR'' Lz hw
    rw [hLz] at this
    exact this

  have hsum : ∀ β : k.Ch B.R.m, ∑ c, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f
      (lowOf I l Z u (fun z => k.rd B.R.m β ψ ⟨z.1, z.2⟩ ((g.oT B.R.m rfl).emb (h c, 1)))) = ε * tl ψ f := by
    intro β
    have hev : ∀ c y, A.rd R.θ B.R.m le_rfl (ι B.R.m β) ψ y ((g.oT B.R.m rfl).emb (h c, 1)) = (I.per l u a).evz ψ c y :=
      fun c y => (GlobalTheory.AdForm.rd_emb_evz I hI hP l Z u a Ch₀ A hIs R.θ hX.inf _ hTop.emb bad K hRP (ι B.R.m β)).2 ψ hψF c (h c) (hh c) y
    have hterm : ∀ c, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f
        (lowOf I l Z u (fun z => k.rd B.R.m β ψ ⟨z.1, z.2⟩ ((g.oT B.R.m rfl).emb (h c, 1)))) =
        ε * (I.per l u a).period (eW.symm (Pi.single c (eW Lz c))) (G' f) := by
      intro c
      have hne : (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.card_pos (α := (I.fm l u a).stabilizer₂ c)).ne'
      have e2 : (fun z : FrN (I.rec7 l Z) (B.R.N B.R.m) => k.rd B.R.m β ψ ⟨z.1, z.2⟩ ((g.oT B.R.m rfl).emb (h c, 1))) =
          fun y' => (I.per l u a).evz ψ c ⟨y'.1, y'.2⟩ := by
        funext z
        exact (congrFun (hC.rdq B.R.m le_rfl β ψ _) _).trans (hev c _)
      rw [e2, ellTop_apply, hst c, heL c]
      field_simp
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.mul_sum, ← LinearMap.sum_apply, ← map_sum, ← map_sum]
    have e3 : ∑ c, Pi.single c (eW Lz c) = eW Lz := Finset.univ_sum_single _
    rw [e3, LinearEquiv.symm_apply_apply, ← hper, hLz]
    rfl
  have hsub : Subsingleton (k.Ch B.R.m) :=
    ⟨fun β β' => hC.live.inj B.R.m ((GlobalTheory.AdForm.TwTest.subsingleton_top hIs).elim _ _)⟩
  rw [hTop.cP]
  have htail : ∀ hm, (tupOf R P u g t r k tl).tail _ hm ψ f = tl ψ f := fun _ => rfl
  rw [htail]
  refine (congrArg (fun S => (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * S) (Finset.sum_congr rfl fun β _ => hsum β)).trans ?_
  have e1 : ∀ {α : Type} (inst : Fintype α), (∀ a b : α, a = b) → α → ∀ x : ℂ,
      @Finset.sum α ℂ _ (@Finset.univ α inst) (fun _ => x) = x := by
    intro α inst hs a x
    haveI : Unique α := ⟨⟨a⟩, fun b => hs _ _⟩
    exact Fintype.sum_unique _
  have e0 : ∀ {α : Type} (inst : Fintype α), IsEmpty α → ∀ x : ℂ,
      @Finset.sum α ℂ _ (@Finset.univ α inst) (fun _ => x) = 0 := by
    intro α inst hE x
    rw [Finset.univ_eq_empty, Finset.sum_empty]
  rcases isEmpty_or_nonempty (k.Ch B.R.m) with hE | hne
  · have h0 : ψ = 0 := by
      funext c
      obtain ⟨β, -⟩ := hC.live.last (A.chOf B.R.m c)
      exact (hE.false β).elim
    have h1 : tl ψ f = 0 := by
      rw [← hper, h0]
      show ((I.per l u a).period ((I.per l u a).lowerMap ((I.per l u a).evz 0))) (G' f) = 0
      simp only [map_zero, LinearMap.zero_apply]
    exact (congrArg (fun S => (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * S) (e0 _ hE _)).trans (by rw [h1]; ring)
  · obtain ⟨β₀⟩ := hne
    exact (congrArg (fun S => (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * S) (e1 _ (fun a b => hsub.elim a b) β₀ _)).trans (by ring)

end GlobalTheory.AdForm
