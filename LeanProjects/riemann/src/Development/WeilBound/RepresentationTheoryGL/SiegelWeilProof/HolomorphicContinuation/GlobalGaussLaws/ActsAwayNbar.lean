import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CompAtMulOfOne

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open AW

namespace AwayH

variable {D : D7} {n : ℕ}

def ActsAway {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (τ : D.what₂.Tau)
    (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (x : G D n) : Prop :=
  ∃ A : (Mx D V.rank n → ℂ) → (Mx D V.rank n → ℂ), ∀ Ψ (hΨ : AwayCls θ τ fr Ψ), AwayCls θ τ fr (A Ψ) ∧
    ∀ f (hf : IsSch f), (ω x ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr f (A Ψ)

section

variable {θ : InfFam D} {V : HSp D} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {τ : D.what₂.Tau}
  {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem mk_eq_tens {Φ : schwartzA θ V.rank n} {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ)
    {f : (Fin V.rank → Fin n → ℂ) → ℂ} (hf : IsSch f) (h : Φ.1 = tens θ τ fr f Ψ) : Φ = ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ :=
  Subtype.ext h

theorem actsAway_one : ActsAway ω τ fr 1 :=
  ⟨id, fun Ψ hΨ => ⟨hΨ, fun f hf => by simp [map_one]⟩⟩

theorem actsAway_mul {x y : G D n} (hx : ActsAway ω τ fr x) (hy : ActsAway ω τ fr y) : ActsAway ω τ fr (x * y) := by
  obtain ⟨Ax, hAx⟩ := hx
  obtain ⟨Ay, hAy⟩ := hy
  refine ⟨fun Ψ => Ax (Ay Ψ), fun Ψ hΨ => ⟨(hAx _ (hAy Ψ hΨ).1).1, fun f hf => ?_⟩⟩
  rw [map_mul, Module.End.mul_apply, mk_eq_tens (hAy Ψ hΨ).1 hf ((hAy Ψ hΨ).2 f hf), (hAx _ (hAy Ψ hΨ).1).2 f hf]

theorem awayCls_smul {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ) (β : ℂ) :
    AwayCls θ τ fr (fun x => β * Ψ x) := by
  refine ⟨fun x x' h1 h2 => by show β * Ψ x = β * Ψ x'; rw [hΨ.1 x x' h1 h2], fun f hf => ?_⟩
  have : tens θ τ fr f (fun x => β * Ψ x) = β • tens θ τ fr f Ψ := by
    funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring
  rw [this]; exact Submodule.smul_mem _ β (hΨ.2 f hf)

variable {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {μ : Measure (Mx D V.rank n)}

theorem actsAway_n (hω : IsWeilSch ψ χ θ V μ ω) (hθ : IsInfFam θ) {x : G D n} (hx : IsTrivAt θ τ x) {b : Mx D n n}
    (h : mat x = blk4 1 b 0 1) : ActsAway ω τ fr x := by
  have hb := compAt_b_zero hx h
  let e : Mx D V.rank n → ℂ := fun x0 => ψ (halfTr (Matrix.trace (b ⬝ inner V x0 x0 : Mx D n n)))
  have key : ∀ Φ : schwartzA θ V.rank n, (ω x Φ).1 = fun x0 => e x0 * Φ.1 x0 :=
    fun Φ => funext fun x0 => hω.unip x b h Φ x0
  refine ⟨fun Ψ x0 => e x0 * Ψ x0, fun Ψ hΨ => ?_⟩
  have hform : ∀ f (hf : IsSch f),
      (ω x ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr f (fun x0 => e x0 * Ψ x0) := by
    intro f hf
    rw [key]
    funext x0
    simp only [tens]
    ring
  refine ⟨⟨fun x0 x0' h1 h2 => ?_, fun f hf => ?_⟩, hform⟩
  · show e x0 * Ψ x0 = e x0' * Ψ x0'
    have he : e x0 = e x0' := by
      show ψ _ = ψ _
      rw [unipArg_away hθ V hb ⟨h1, h2⟩]
    rw [he, hΨ.1 x0 x0' h1 h2]
  · rw [← hform f hf]; exact (ω x _).2

theorem actsAway_m (hω : IsWeilSch ψ χ θ V μ ω) {x : G D n} (hx : IsTrivAt θ τ x) {a d : Mx D n n}
    (h : mat x = blk4 a 0 0 d) : ActsAway ω τ fr x := by
  obtain ⟨a', ha', hd⟩ := levi_blocks x h
  have ha1 : compAt θ τ a'.1 = 1 := by rw [ha']; exact compAt_a_one hx h
  let cst : ℂ := (χ (Matrix.GeneralLinearGroup.det a') : ℂ) *
    npow (absA D (Matrix.GeneralLinearGroup.det a')) ((V.rank : ℂ) / 2)
  have hm : mat x = blk4 a'.1 0 0 (adj (a'⁻¹).1) := by rw [h, ha', hd]
  have key : ∀ Φ : schwartzA θ V.rank n, (ω x Φ).1 = fun x0 : Mx D V.rank n => cst * Φ.1 (x0 ⬝ a'.1) :=
    fun Φ => funext fun x0 => hω.levi x a' hm Φ x0
  refine ⟨fun Ψ (x0 : Mx D V.rank n) => cst * Ψ (x0 ⬝ a'.1), fun Ψ hΨ => ?_⟩
  have hform : ∀ f (hf : IsSch f),
      (ω x ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr f (fun x0 : Mx D V.rank n => cst * Ψ (x0 ⬝ a'.1)) := by
    intro f hf
    rw [key]
    funext x0
    simp only [tens]
    rw [compAt_mul_of_one x0 a'.1 ha1]
    ring
  refine ⟨⟨fun x0 x0' h1 h2 => ?_, fun f hf => ?_⟩, hform⟩
  · have hag := agree_mul_right a'.1 (⟨h1, h2⟩ : AgreeAway θ τ x0 x0')
    show cst * Ψ (x0 ⬝ a'.1) = cst * Ψ (x0' ⬝ a'.1)
    rw [hΨ.1 _ _ hag.1 hag.2]
  · rw [← hform f hf]; exact (ω x _).2

end

theorem actsAway_nbar (hFT : FTfact) {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}
    (hcx : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) {x : G D n} (hx : IsTrivAt θ τ x) {c : Mx D n n}
    (h : mat x = blk4 1 0 c 1) : ActsAway ω τ fr x := by
  obtain ⟨w, hw⟩ := exists_w D n
  have hy : mat (w⁻¹ * x * w) = blk4 1 (-c) 0 1 := mat_w_conj hw h
  have hyt : IsTrivAt θ τ (w⁻¹ * x * w) := trivAt_conj w hx
  obtain ⟨An, hAn⟩ := actsAway_n (fr := fr) hcx.hω hcx.hθ hyt hy
  obtain ⟨κ, A, A', hκ, hF⟩ := hFT D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx w hw
  have hxy : x = w * (w⁻¹ * x * w) * w⁻¹ := by group
  let S : ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ) :=
    fun f u => κ * ftLoc ε (tLoc l τ) (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) u
  have chain : ∀ (B : (Mx D V.rank n → ℂ) → (Mx D V.rank n → ℂ)) (z : G D n),
      (∀ Ψ (hΨ : AwayCls θ τ fr Ψ), AwayCls θ τ fr (B Ψ) ∧
        ∀ f (hf : IsSch f), (ω z ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr f (B Ψ)) →
      ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) f (hf : IsSch f),
        (ω (w * z * w⁻¹) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (S f) (A (B (A' Ψ))) := by
    intro B z hB Ψ hΨ f hf
    obtain ⟨_, hA'1, hfs⟩ := hF Ψ hΨ
    obtain ⟨_, hs2, _, e2⟩ := hfs f hf
    have hB1 := hB (A' Ψ) hA'1
    obtain ⟨_, _, hfs2⟩ := hF (B (A' Ψ)) hB1.1
    obtain ⟨_, _, e3, _⟩ := hfs2 _ hs2
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, mk_eq_tens hA'1 hs2 e2,
      mk_eq_tens hB1.1 hs2 (hB1.2 _ hs2), e3]
  have ident : ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) f (hf : IsSch f),
      tens θ τ fr f Ψ = tens θ τ fr (S f) (A (A' Ψ)) := by
    intro Ψ hΨ f hf
    have := chain id 1 (fun Ψ hΨ => ⟨hΨ, fun f hf => by simp [map_one]⟩) Ψ hΨ f hf
    simpa using this
  have hdet : IsUnit fr.det := hcx.hfr.1
  classical
  by_cases hex : ∃ Ψ0 : Mx D V.rank n → ℂ, AwayCls θ τ fr Ψ0 ∧ ∃ x0 : Mx D V.rank n, Ψ0 x0 ≠ 0
  · obtain ⟨Ψ0, h0, x0, hne⟩ := hex
    have hAA0 : AwayCls θ τ fr (A (A' Ψ0)) := (hF _ (hF Ψ0 h0).2.1).1
    obtain ⟨f0, hf0, hf0ne⟩ := exists_sch_ne (fr⁻¹ * compAt θ τ x0)
    have e0 := congrFun (ident Ψ0 h0 f0 hf0) x0
    simp only [tens] at e0
    have hα : A (A' Ψ0) x0 ≠ 0 := by
      intro h0'
      rw [h0', mul_zero] at e0
      exact mul_ne_zero hf0ne hne e0
    let β : ℂ := Ψ0 x0 / A (A' Ψ0) x0
    have hS : ∀ f, IsSch f → ∀ u, S f u = β * f u := by
      intro f hf u
      obtain ⟨z, hz⟩ := exists_compAt (τ := τ) hcx.hθ (fr * Matrix.of u)
      obtain ⟨x1, hx1, hag⟩ := exists_change_tau (τ := τ) hcx.hθ x0 z
      have hu : fr⁻¹ * compAt θ τ x1 = Matrix.of u := by
        rw [hx1, hz, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
      have e := congrFun (ident Ψ0 h0 f hf) x1
      simp only [tens] at e
      rw [hu, h0.1 x1 x0 hag.1 hag.2, hAA0.1 x1 x0 hag.1 hag.2] at e
      have e' : f u * Ψ0 x0 = S f u * A (A' Ψ0) x0 := e
      show S f u = Ψ0 x0 / A (A' Ψ0) x0 * f u
      field_simp
      linear_combination -e'
    refine ⟨fun Ψ x0 => β * A (An (A' Ψ)) x0, fun Ψ hΨ => ?_⟩
    have hA'1 := (hF Ψ hΨ).2.1
    have hAn1 := (hAn (A' Ψ) hA'1).1
    have hAA := (hF _ hAn1).1
    refine ⟨awayCls_smul hAA β, fun f hf => ?_⟩
    rw [hxy, chain An _ hAn Ψ hΨ f hf]
    funext x1
    simp only [tens]
    have hh : S f (fr⁻¹ * compAt θ τ x1) = β * f (fr⁻¹ * compAt θ τ x1) := hS f hf _
    rw [hh]
    ring
  · push Not at hex
    refine ⟨fun _ _ => 0, fun Ψ hΨ => ⟨⟨fun _ _ _ _ => rfl, fun f hf => ?_⟩, fun f hf => ?_⟩⟩
    · have : tens θ τ fr f (fun _ => (0 : ℂ)) = 0 := by funext x0; simp [tens]
      rw [this]; exact Submodule.zero_mem _
    · have h0 : (⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ : schwartzA θ V.rank n) = 0 :=
        Subtype.ext (funext fun x0 => by simp [tens, hex Ψ hΨ x0])
      rw [h0, map_zero]
      funext x0
      simp [tens]

end AwayH

open AwayH

theorem awayAct_of : GenA → FTfact → DecompAway → AwayAct := by
  intro hG hFT hDA D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx x hx
  have hmem := mem_closure_AG hG hDA hcx.hθ hcx.hι x hx
  clear hx
  have key : ActsAway ω τ fr x := by
    induction hmem using Submonoid.closure_induction with
    | mem y hy =>
      obtain ⟨hyt, ⟨b, hb⟩ | ⟨a, d, hm⟩ | ⟨c, hc⟩⟩ := hy
      · exact actsAway_n hcx.hω hcx.hθ hyt hb
      · exact actsAway_m hcx.hω hyt hm
      · exact actsAway_nbar hFT hcx hyt hc
    | one => exact actsAway_one
    | mul y z _ _ hy hz => exact actsAway_mul hy hz
  exact key

end PositivityTheory.Rg.Sw.Glob
