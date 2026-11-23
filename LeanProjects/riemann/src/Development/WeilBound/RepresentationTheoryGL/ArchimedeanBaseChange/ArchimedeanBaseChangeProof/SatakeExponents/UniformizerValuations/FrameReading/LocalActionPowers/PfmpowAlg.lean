import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.PfmpowLoc
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.PfmpowLev

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

set_option linter.unusedSectionVars false

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem fixed_mono {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    {K K' : Subgroup G} (hle : K' ≤ K) {v : V} (hv : v ∈ fixed ρ K) : v ∈ fixed ρ K' := by
  simp only [GlobalTheory.PRep.fixed, GlobalTheory.PRep.eig, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_ofPred_eq] at hv ⊢
  intro h
  exact hv ⟨h.1, hle h.2⟩

theorem isHecke_zero {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) : IsHecke K (fun _ : G => (0 : ℂ)) :=
  ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem isTestFunction_modify {φ ψ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (hφ : IsTestP φ) (T : Finset (Pl E))
    (V₁ : ∀ w : Pl E, Subgroup (GLw a w)) (V₂ : ∀ w : Pl E, Subgroup (GLw b w))
    (hV₁ : ∀ w, IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) (V₁ w)) (hV₂ : ∀ w, IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) (V₂ w))
    (hout : ∀ w, w ∉ T → ψ w = φ w) (hin : ∀ w ∈ T, IsHecke ((V₁ w).prod (V₂ w)) (ψ w)) : IsTestP ψ := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hT⟩ := hφ
  refine ⟨fun w => if w ∈ T then V₁ w else K₁ w, fun w => if w ∈ T then V₂ w else K₂ w, ⟨fun w => ?_, ?_⟩,
    ⟨fun w => ?_, ?_⟩, fun w => ?_, ?_⟩
  · by_cases h : w ∈ T
    · simp only [h, if_true]; exact hV₁ w
    · simp only [h, if_false]; exact hK₁.1 w
  · filter_upwards [hK₁.2, T.finite_toSet.compl_mem_cofinite] with w hw hwT
    simp only [Set.mem_compl_iff, Finset.mem_coe] at hwT
    simp only [hwT, if_false, hw]
  · by_cases h : w ∈ T
    · simp only [h, if_true]; exact hV₂ w
    · simp only [h, if_false]; exact hK₂.1 w
  · filter_upwards [hK₂.2, T.finite_toSet.compl_mem_cofinite] with w hw hwT
    simp only [Set.mem_compl_iff, Finset.mem_coe] at hwT
    simp only [hwT, if_false, hw]
  · by_cases h : w ∈ T
    · simp only [h, if_true]; exact hin w h
    · simp only [h, if_false]; rw [hout w h]; exact hT.1 w
  · filter_upwards [hT.2, T.finite_toSet.compl_mem_cofinite] with w hw hwT
    simp only [Set.mem_compl_iff, Finset.mem_coe] at hwT
    rw [hout w hwT, hw]

theorem hasLev_zero : HasLev (0 : H E a b → ℂ) :=
  ⟨⊤, by rw [Subgroup.coe_top]; exact isOpen_univ, fun _ _ _ => rfl⟩

theorem hasLev_add {G G' : H E a b → ℂ} (h : HasLev G) (h' : HasLev G') : HasLev (G + G') := by
  obtain ⟨U, hU, hG⟩ := h
  obtain ⟨U', hU', hG'⟩ := h'
  refine ⟨U ⊓ U', by rw [Subgroup.coe_inf]; exact hU.inter hU', fun u hu x => ?_⟩
  have hu' := Subgroup.mem_inf.1 hu
  simp only [Pi.add_apply, hG u hu'.1 x, hG' u hu'.2 x]

theorem hasLev_sum {ι : Type} (s : Finset ι) (g : ι → H E a b → ℂ) (h : ∀ i ∈ s, HasLev (g i)) :
    HasLev (∑ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (hasLev_zero (E := E) (a := a) (b := b))
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact hasLev_add (h x (Finset.mem_insert_self x s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem uniform_lev {ι : Type} [Finite ι] (G : ι → H E a b → ℂ) (h : ∀ i, HasLev (G i)) :
    ∃ U : Subgroup (Hf E a b), IsOpen (U : Set (Hf E a b)) ∧ ∀ i, ∀ u ∈ U, ∀ x, G i (x * finH u) = G i x := by
  choose U hU hG using h
  refine ⟨⨅ i, U i, ?_, fun i u hu x => hG i u (Subgroup.mem_iInf.1 hu i) x⟩
  rw [Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite hU

theorem convF_congr {A A' κ : Type} [Fintype κ] [MeasurableSpace (Hf E a b)] (ν : Measure (Hf E a b))
    (ψ : Matrix κ κ (Hf E a b → ℂ)) (G : A × κ → H E a b → ℂ) (G' : A' × κ → H E a b → ℂ) (p : A) (q : A')
    (h : ∀ z, G (p, z) = G' (q, z)) (x : κ) : convF ν ψ G (p, x) = convF ν ψ G' (q, x) := by
  funext y
  simp only [convF, h]

theorem convF_zero {A κ : Type} [Fintype κ] [MeasurableSpace (Hf E a b)] (ν : Measure (Hf E a b))
    (ψ : Matrix κ κ (Hf E a b → ℂ)) : convF ν ψ (0 : A × κ → H E a b → ℂ) = 0 := by
  funext i y
  simp [convF]

theorem iter_restrict {A κ : Type} [Fintype κ] [MeasurableSpace (Hf E a b)] (ν : Measure (Hf E a b))
    (ψ : Matrix κ κ (Hf E a b → ℂ)) (F : A × κ → H E a b → ℂ) (p : A) (k : ℕ) (x : κ) :
    (convF ν ψ)^[k] F (p, x) = (convF ν ψ)^[k] (fun i : Unit × κ => F (p, i.2)) ((), x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact convF_congr ν ψ _ _ p () (fun z => ih z) x

section
variable {κ : Pl E → Type} [∀ w, Fintype (κ w)]

def pw (M : LM κ a b) : ℕ → LM κ a b
  | 0 => M
  | k + 1 => M.mul (pw M k)

theorem mul_m (M M' : LM κ a b) (w : Pl E) (x y : κ w) :
    (M.mul M').m w x y = ∑ z, mconv (M.m w x z) (M'.m w z y) := rfl

theorem mul_s (M M' : LM κ a b) (w : Pl E) : (M.mul M').s w = mconv (M.s w) (M'.s w) := rfl

theorem product_torus_component (M M' : LM κ a b) (w : Pl E) : (M.mul M').t w = mconv (M.t w) (M'.t w) := rfl

def dg (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w : Pl E) (x y : κ w) : GLw a w × GLw b w → ℂ :=
  if x = y then idem (V w) else fun _ => 0

def only0 (L : LM κ a b) (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w₀ : Pl E) : LM κ a b :=
  ⟨fun w x y => if w = w₀ then L.m w x y else dg V w x y, L.s, L.t⟩

def rest1 (L : LM κ a b) (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w₀ : Pl E) : LM κ a b :=
  ⟨fun w x y => if w = w₀ then dg V w x y else L.m w x y, L.s, L.t⟩

theorem dg_mul_left (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w : Pl E) (x : κ w)
    (f : κ w → GLw a w × GLw b w → ℂ) : ∑ z, mconv (dg V w x z) (f z) = mconv (idem (V w)) (f x) := by
  rw [Finset.sum_eq_single x]
  · simp [dg]
  · intro z _ hz
    simp only [dg, if_neg (Ne.symm hz)]
    exact mconv_zero_left _
  · simp

theorem dg_mul_right (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w : Pl E) (y : κ w)
    (f : κ w → GLw a w × GLw b w → ℂ) : ∑ z, mconv (f z) (dg V w z y) = mconv (f y) (idem (V w)) := by
  rw [Finset.sum_eq_single y]
  · simp [dg]
  · intro z _ hz
    simp only [dg, if_neg hz]
    exact mconv_zero_right _
  · simp

theorem mconv_idem_dg {V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)} {w : Pl E}
    (hV : IsOpen (V w : Set (GLw a w × GLw b w))) (hle : V w ≤ K2 a b w) (x y : κ w) :
    mconv (idem (V w)) (dg V w x y) = dg V w x y := by
  unfold dg
  split_ifs
  · exact mconv_idem_left hV hle fun v hv g => idem_left hv g
  · exact mconv_zero_right _

theorem stabilizerDilationWeights_dualIsotropicVector (M : LM κ a b) (W : ∀ w : Pl E, Subgroup (GLw a w × GLw b w))
    (hW : ∀ w, IsOpen (W w : Set (GLw a w × GLw b w)) ∧ W w ≤ K2 a b w) (hs : ∀ w, M.s w = idem (W w)) :
    ∀ k w, (pw M k).s w = idem (W w) := by
  intro k
  induction k with
  | zero => exact hs
  | succ k ih =>
    intro w
    show mconv (M.s w) ((pw M k).s w) = _
    rw [hs, ih]
    exact mconv_idem_left (hW w).1 (hW w).2 fun v hv g => idem_left hv g

theorem power_torus_component_idempotent (M : LM κ a b) (W : ∀ w : Pl E, Subgroup (GLw a w × GLw b w))
    (hW : ∀ w, IsOpen (W w : Set (GLw a w × GLw b w)) ∧ W w ≤ K2 a b w) (ht : ∀ w, M.t w = idem (W w)) :
    ∀ k w, (pw M k).t w = idem (W w) := by
  intro k
  induction k with
  | zero => exact ht
  | succ k ih =>
    intro w
    show mconv (M.t w) ((pw M k).t w) = _
    rw [ht, ih]
    exact mconv_idem_left (hW w).1 (hW w).2 fun v hv g => idem_left hv g

theorem pw_m_congr (M M' : LM κ a b) (w : Pl E) (h : M.m w = M'.m w) : ∀ k, (pw M k).m w = (pw M' k).m w := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    show (fun x y => ∑ z, mconv (M.m w x z) ((pw M k).m w z y)) =
      fun x y => ∑ z, mconv (M'.m w x z) ((pw M' k).m w z y)
    rw [h, ih]

theorem pw_dg (M : LM κ a b) (V : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (w : Pl E)
    (hV : IsOpen (V w : Set (GLw a w × GLw b w))) (hle : V w ≤ K2 a b w) (h : M.m w = dg V w) :
    ∀ k, (pw M k).m w = dg V w := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    funext x y
    show ∑ z, mconv (M.m w x z) ((pw M k).m w z y) = _
    rw [h, ih, dg_mul_left V w x (fun z => dg V w z y)]
    exact mconv_idem_dg hV hle x y

theorem pw_left (M : LM κ a b) (w : Pl E) (W : Subgroup (GLw a w × GLw b w))
    (h : ∀ x y, ∀ v ∈ W, ∀ g, M.m w x y (v * g) = M.m w x y g) :
    ∀ k x y, ∀ v ∈ W, ∀ g, (pw M k).m w x y (v * g) = (pw M k).m w x y g := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    intro x y v hv g
    show (∑ z, mconv (M.m w x z) ((pw M k).m w z y)) (v * g) = (∑ z, mconv (M.m w x z) ((pw M k).m w z y)) g
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun z _ => mconv_left (fun g' => h x z v hv g') g

theorem pw_right (M : LM κ a b) (w : Pl E) (W : Subgroup (GLw a w × GLw b w))
    (h : ∀ x y, ∀ v ∈ W, ∀ g, M.m w x y (g * v) = M.m w x y g) :
    ∀ k x y, ∀ v ∈ W, ∀ g, (pw M k).m w x y (g * v) = (pw M k).m w x y g := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    intro x y v hv g
    show (∑ z, mconv (M.m w x z) ((pw M k).m w z y)) (g * v) = (∑ z, mconv (M.m w x z) ((pw M k).m w z y)) g
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun z _ => mconv_right (fun g' => ih z y v hv g') g

end

section
variable {κ : Pl E → Type} [∀ w, Fintype (κ w)]

theorem pw_ok (hA : FmAlg) (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w)
    (hS : IsSection S) (hP : (↑P : Set (Pl E)) ⊆ S) (M : LM κ B.a B.b) (hM : M.Ok P) : ∀ k, (pw M k).Ok P := by
  intro k
  induction k with
  | zero => exact hM
  | succ k ih => exact (hA E κ S P B e hS hP M (pw M k) hM ih).2.1

theorem iter_pw (hA : FmAlg) (hC : ConvMul) (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E)
    (e : B.κ ≃ ∀ w : P, κ w) (hS : IsSection S) (hP : (↑P : Set (Pl E)) ⊆ S) (M : LM κ B.a B.b) (hM : M.Ok P)
    {A : Type} (G : A × B.κ → H E B.a B.b → ℂ) (U : Subgroup (Hf E B.a B.b)) (hU : IsOpen (U : Set (Hf E B.a B.b)))
    (hG : ∀ i, ∀ u ∈ U, ∀ x, G i (x * finH u) = G i x) :
    ∀ k, (convF B.ν (fm S P B e M))^[k + 1] G = convF B.ν (fm S P B e (pw M k)) G := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hk := pw_ok hA S P B e hS hP M hM k
    obtain ⟨h1, -, h3, -⟩ := hA E κ S P B e hS hP M (pw M k) hM hk
    have h2 := (hA E κ S P B e hS hP (pw M k) M hk hM).1
    rw [← (hC E B A _ _ U G h1 h2 hU hG).1, h3]
    rfl

end

end PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

end
