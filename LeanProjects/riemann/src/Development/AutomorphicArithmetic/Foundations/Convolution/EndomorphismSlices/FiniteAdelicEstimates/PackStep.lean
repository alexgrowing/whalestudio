import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.MultOfKer
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HeckeFunctionIsHecke
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.IdmAct
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.KgFacts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.GelOfHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.EigArch

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem slice_left {X Y : Type} (W₁ : Submodule ℂ (X → ℂ)) (W₂ : Submodule ℂ (Y → ℂ)) (y : Y) (F : X × Y → ℂ)
    (h : F ∈ Submodule.span ℂ {f : X × Y → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun x => F (x, y)) ∈ W₁ := by
  induction h using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨w₁, h₁, w₂, _, rfl⟩ := hg
    have := W₁.smul_mem (w₂ y) h₁
    convert this using 1
    funext x
    simp [mul_comm]
  | zero => exact W₁.zero_mem
  | add g g' _ _ hg hg' => exact W₁.add_mem hg hg'
  | smul c g _ hg => exact W₁.smul_mem c hg

private theorem slice_right {X Y : Type} (W₁ : Submodule ℂ (X → ℂ)) (W₂ : Submodule ℂ (Y → ℂ)) (x : X) (F : X × Y → ℂ)
    (h : F ∈ Submodule.span ℂ {f : X × Y → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun y => F (x, y)) ∈ W₂ := by
  induction h using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨w₁, _, w₂, h₂, rfl⟩ := hg
    exact W₂.smul_mem (w₁ x) h₂
  | zero => exact W₂.zero_mem
  | add g g' _ _ hg hg' => exact W₂.add_mem hg hg'
  | smul c g _ hg => exact W₂.smul_mem c hg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

private theorem type_left {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ} (h : TypeH K₁ K₂ W₁ W₂ F)
    (m₂ : GA E b) (φ : Sm E a) (hφ : φ.1 = fun x => F (x, m₂)) : TypeB K₁ W₁ φ := by
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · rw [hφ]
    simpa using h.1 u hu 1 K₂.one_mem (g, m₂)
  · rw [hφ]
    simpa using slice_left W₁ W₂ 1 _ (h.2 (g, m₂))

private theorem type_right {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ} (h : TypeH K₁ K₂ W₁ W₂ F)
    (m₁ : GA E a) (φ : Sm E b) (hφ : φ.1 = fun x => F (m₁, x)) : TypeB K₂ W₂ φ := by
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · rw [hφ]
    simpa using h.1 1 K₁.one_mem u hu (m₁, g)
  · rw [hφ]
    simpa using slice_right W₁ W₂ 1 _ (h.2 (m₁, g))

private theorem gen_a {l₁ : InfinitePlace E → DomWeight a} {l₂ : InfinitePlace E → DomWeight b} {D : Dom E a b} (A : Ar l₁ l₂ D)
    (S : Set (Pl E)) {Z : Finset (Pl E)} (L : Lv a b Z) (T : Finset (Pl E)) (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1)))
    (v : InfinitePlace E) (r : Bool) (m : ℕ) :
    (A.gen S L T e₁ e₂ (.inr (.inl (v, r, m, false)))).Φ =
      tens (Function.update (A.ka []) v (A.ka [(r, m)] v)) (A.kb []) (A.idm S L) := by
  have h1 : (fun w => A.ka (if w = v ∧ false = false then [(r, m)] else []) w) = Function.update (A.ka []) v (A.ka [(r, m)] v) := by
    funext w
    by_cases h : w = v
    · subst h
      simp
    · simp [h]
  have h2 : (fun w => A.kb (if w = v ∧ false = true then [(r, m)] else []) w) = A.kb [] := by
    funext w
    simp
  rw [← h1, ← h2]
  rfl

private theorem gen_b {l₁ : InfinitePlace E → DomWeight a} {l₂ : InfinitePlace E → DomWeight b} {D : Dom E a b} (A : Ar l₁ l₂ D)
    (S : Set (Pl E)) {Z : Finset (Pl E)} (L : Lv a b Z) (T : Finset (Pl E)) (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1)))
    (v : InfinitePlace E) (r : Bool) (m : ℕ) :
    (A.gen S L T e₁ e₂ (.inr (.inl (v, r, m, true)))).Φ =
      tens (A.ka []) (Function.update (A.kb []) v (A.kb [(r, m)] v)) (A.idm S L) := by
  have h1 : (fun w => A.kb (if w = v ∧ true = true then [(r, m)] else []) w) = Function.update (A.kb []) v (A.kb [(r, m)] v) := by
    funext w
    by_cases h : w = v
    · subst h
      simp
    · simp [h]
  have h2 : (fun w => A.ka (if w = v ∧ true = false then [(r, m)] else []) w) = A.ka [] := by
    funext w
    simp
  rw [← h1, ← h2]
  rfl

theorem packStep : PackStep := by
  intro E _ _ _ a b l₁ l₂
  obtain ⟨W₁, W₂, f₁, f₂, hW⟩ := PositivityTheory.Rg.BcB.CG.pack_holds E a b (Ml l₁) (Ml l₂)
  refine ⟨W₁, W₂, f₁, f₂, ?_⟩
  intro D A S Z L hS hZ T e₁ e₂ s f hs hE
  haveI := A.ha
  haveI := A.hb
  haveI := A.hν
  haveI : BorelSpace (G a) := ⟨rfl⟩
  haveI : BorelSpace (G b) := ⟨rfl⟩
  haveI : BorelSpace (Hf E a b) := ⟨rfl⟩
  obtain ⟨-, -, hOk, -, -⟩ := ptOk E a b l₁ l₂ D A
  obtain ⟨hψ, -, -, -, -, -, hhk, -⟩ := hkMul E a b l₁ l₂ D A S Z L hS hZ
  obtain ⟨hlev, -, hfix⟩ := idmAct E a b l₁ l₂ D A S Z L hS hZ
  have hK₁ := kgFacts E a S Z L.L₁ hS hZ (fun w => ⟨L.open₁ w, L.le₁ w⟩) (fun w hw => (L.off w hw).1)
  have hK₂ := kgFacts E b S Z L.L₂ hS hZ (fun w => ⟨L.open₂ w, L.le₂ w⟩) (fun w hw => (L.off w hw).2)
  have h0 := hOk (fun _ => []) (fun _ => []) (A.idm S L) hψ
  have hka : IsMults A.μa (A.ka []) (fun v => A.valW []) A.T := h0.ka
  have hkb : IsMults A.μb (A.kb []) (fun v => A.valW []) A.T := h0.kb
  have he : PositivityTheory.Rg.BcB.E.conv D.μ (tens (A.ka []) (A.kb []) (A.idm S L)) f = s (.inl ()) • f := hE.eig (.inl ())
  have hea : ∀ v r m, PositivityTheory.Rg.BcB.E.conv D.μ (tens (Function.update (A.ka []) v (A.ka [(r, m)] v)) (A.kb []) (A.idm S L)) f =
      s (.inr (.inl (v, r, m, false))) • f := fun v r m => by
    have h1 := hE.eig (.inr (.inl (v, r, m, false)))
    rw [gen_a] at h1
    exact h1
  have heb : ∀ v r m, PositivityTheory.Rg.BcB.E.conv D.μ (tens (A.ka []) (Function.update (A.kb []) v (A.kb [(r, m)] v)) (A.idm S L)) f =
      s (.inr (.inl (v, r, m, true))) • f := fun v r m => by
    have h1 := hE.eig (.inr (.inl (v, r, m, true)))
    rw [gen_b] at h1
    exact h1
  obtain ⟨M, hM⟩ := hE.wl
  obtain ⟨χa, χb, ga, gb, hEig, hty, s₁, s₂, au₁, au₂, ic₁, ic₂⟩ :=
    hW D A.μa A.μb A.ν Unit (A.ka []) (A.kb []) (fun v => A.valW []) (fun v => A.valW []) A.T (A.idm S L) A.bump
      (fun r m => A.ka [(r, m)]) (fun r m => A.kb [(r, m)]) (Kg S L.L₁) (Kg S L.L₂) M f (s (.inl ()))
      (fun v r m => s (.inr (.inl (v, r, m, false)))) (fun v r m => s (.inr (.inl (v, r, m, true)))) A.compat hka hkb hψ A.isBump
      (A.kera []) (A.kerb []) (fun r m v => A.kera [(r, m)] v) (fun r m v => A.kerb [(r, m)] v) hK₁.1 hK₂.1 hlev hE.cont hE.ne
      hE.inv hM hs he hea heb
  have hlevel : LevelF (Kg S L.L₁) (Kg S L.L₂) f := fun i u₁ h₁ u₂ h₂ x => (hty i).1 u₁ h₁ u₂ h₂ x
  have hR : Repr D (A.ka []) (A.kb []) (A.idm S L) f := ⟨hE.cont, s (.inl ()), hs, he⟩
  have hact : ∀ ψ', IsFinM ψ' → PositivityTheory.Rg.BcB.E.conv D.μ (tens (A.ka []) (A.kb []) ψ') f =
      (valA (fun v => A.valW []) χa * valA (fun v => A.valW []) χb) • convF A.ν ψ' f := fun ψ' h' =>
    actVal_holds E a b D A.μa A.μb A.ν (Ml l₁) (Ml l₂) Unit (A.ka []) (A.ka []) (A.kb []) (A.kb []) _ _ _ _ A.T A.T (A.idm S L) ψ' f
      χa χb A.compat hka hkb hψ hR ⟨s₁, s₂⟩ hEig hka hkb h'
  have hval : valA (fun v => A.valW []) χa * valA (fun v => A.valW []) χb = s (.inl ()) := by
    have h1 := hact _ hψ
    rw [he, hfix f hlevel] at h1
    exact (smul_left_injective ℂ hE.ne h1).symm
  have hfin : ∀ ψ' c', IsFinM ψ' → PositivityTheory.Rg.BcB.E.conv D.μ (tens (A.ka []) (A.kb []) ψ') f = c' • f →
      convF A.ν ψ' f = (c' / s (.inl ())) • f := fun ψ' c' h' e' => by
    have h1 := hact ψ' h'
    rw [e', hval] at h1
    have h2 : convF A.ν ψ' f = (s (.inl ()))⁻¹ • (s (.inl ()) • convF A.ν ψ' f) := by
      rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
    rw [h2, ← h1, smul_smul, inv_mul_eq_div]
  refine ⟨χa, χb, ga, gb, hlevel, ⟨s₁, s₂⟩, ?_, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨i, m₂, e⟩ := id hφ
    exact ⟨au₁ φ hφ, type_left (hty i) m₂ φ e, fun t => ⟨(ic₁ t).1, fun u => (ic₁ t).2 u φ (Submodule.subset_span hφ)⟩⟩
  · intro φ hφ
    obtain ⟨i, m₁, e⟩ := id hφ
    exact ⟨au₂ φ hφ, type_right (hty i) m₁ φ e, fun t => ⟨(ic₂ t).1, fun u => (ic₂ t).2 u φ (Submodule.subset_span hφ)⟩⟩
  · rintro (x | u)
    · exact hfin _ _ (hhk _ _ _).1 (hE.eig (.inr (.inr (.inl x))))
    · exact hfin _ _ (hhk _ _ _).1 (hE.eig (.inr (.inr (.inr u))))

end UpperTheory.Zero.ConvolutionTheory.EB
