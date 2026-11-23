import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOfFiniteOfClosedFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsValuesLineFibre

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open scoped Topology
open Filter

namespace GlobalTheory.ThetaFamily

variable {g m : ℕ} {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : RigLB G}

def IsFibreFrame (L : RigLB G) (y : Sp ℂ ⟶ S) (e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)) (θ : (Fin g → ℂ) → ℂ)
    (fr : L.L.ι → (Fin g → ℂ) → ℂ) : Prop :=
  (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.L.U j}) ∧
  (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.L.U j → fr j z ≠ 0) ∧
  (∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.L.U j ⊓ L.L.U j') →
    fr j z = valAt' (e z) (L.L.U j ⊓ L.L.U j') (L.L.g j j').val * fr j' z) ∧
  (∀ j, ⊤ ≤ e 0 ⁻¹ᵁ L.L.U j →
    fr j 0 = valAt' y ((L.L.pull (eSec G)).U (fun _ => j)) (L.rig.s (fun _ => j)).val) ∧
  ∃ s : (L.L.pull (pullback.fst G.hom y)).Sec, ∀ j z (x : Sp ℂ ⟶ pullback G.hom y),
    x ≫ pullback.fst _ _ = e z → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ e z ⁻¹ᵁ L.L.U j →
    valAt' x ((L.L.pull (pullback.fst G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z

def SpansFibre (L : RigLB G) (y : Sp ℂ ⟶ S) (V : S.Opens) (θ₀ : ∀ j, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.L.U j)) : Prop :=
  ∀ σ : LB.Sec (L.L.pull (pullback.fst G.hom y)), ∃ a : ℂ, ∀ j (x : Sp ℂ ⟶ pullback G.hom y),
    x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (x ≫ pullback.fst _ _) ⁻¹ᵁ L.L.U j →
    valAt' x ((L.L.pull (pullback.fst G.hom y)).U (fun _ => j)) (σ.f (fun _ => j)) =
      a * valAt' (x ≫ pullback.fst _ _) (G.hom ⁻¹ᵁ V ⊓ L.L.U j) (θ₀ j)

theorem isThetaFrame_singleton_iff {y : (Fin m → ℂ) → (Sp ℂ ⟶ S)}
    {e : (Fin m → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G.left)} {θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ} {b : Fin m → ℂ} :
    IsThetaFrame L {b} y e θ ↔ ∃ fr, IsFibreFrame L (y b) (e b) (θ b) fr := by
  constructor
  · rintro ⟨fr, h1, h2, h3, h4, h5⟩
    exact ⟨fun j z => fr j (b, z), fun j => (h1 j).comp (f := fun z => (b, z)) (by fun_prop) fun z hz => ⟨rfl, hz⟩,
      fun j z => h2 j b z rfl, fun j j' z => h3 j j' b z rfl, fun j => h4 j b rfl, h5 b rfl⟩
  · rintro ⟨fr, h1, h2, h3, h4, h5⟩
    refine ⟨fun j bz => fr j bz.2, fun j => (h1 j).comp (f := Prod.snd) (by fun_prop) ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨_, z⟩ ⟨rfl, hz⟩; exact hz
    · rintro j _ z rfl; exact h2 j z
    · rintro j j' _ z rfl; exact h3 j j' z
    · rintro j _ rfl; exact h4 j
    · rintro _ rfl; exact h5

section Fibre

variable {y : Sp ℂ ⟶ S} {e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)} {θ θ' : (Fin g → ℂ) → ℂ} {fr : L.L.ι → (Fin g → ℂ) → ℂ}

theorem exists_chart_point (L : RigLB G) (x : Sp ℂ ⟶ G.left) : ∃ j, ⊤ ≤ x ⁻¹ᵁ L.L.U j := by
  obtain ⟨j, hj⟩ := exists_chart L.isLB (x (default : PrimeSpectrum ℂ))
  exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩

theorem IsFibreFrame.rescale (h : IsFibreFrame L y e θ fr) {ρ : (Fin g → ℂ) → ℂ} (hd : Differentiable ℂ ρ)
    (h0 : ∀ z, ρ z ≠ 0) (hρ : ∀ z, ρ z * θ z = θ' z) :
    IsFibreFrame L y e θ' (fun j z => fr j z * (ρ 0 * (ρ z)⁻¹)) := by
  obtain ⟨h1, h2, h3, h4, s, h5⟩ := h
  refine ⟨fun j => (h1 j).mul ((differentiable_const _).mul (hd.inv h0)).differentiableOn,
    fun j z hz => mul_ne_zero (h2 j z hz) (mul_ne_zero (h0 _) (inv_ne_zero (h0 _))),
    fun j j' z hz => by simp only [h3 j j' z hz, _root_.mul_assoc],
    fun j hj => by simp only [mul_inv_cancel₀ (h0 0), _root_.mul_one, h4 j hj], ?_⟩
  obtain ⟨t, ht⟩ := exists_sec_const_mul (pullback.snd G.hom y) s (ρ 0)
  refine ⟨t, fun j z x x1 x2 hz => ?_⟩
  have hz' : ⊤ ≤ (x ≫ pullback.fst G.hom y) ⁻¹ᵁ L.L.U j := by rw [x1]; exact hz
  rw [ht (fun _ => j) x x2 (fun p hp => mem_pull.2 (hz' hp)), h5 j z x x1 x2 hz, ← hρ]
  have := h0 z
  field_simp

theorem IsFibreFrame.ratio (h : IsFibreFrame L y e θ fr) (he : ∀ z, e z ≫ G.hom = y) (hθ : θ ≠ 0) {V : S.Opens}
    {θ₀ : ∀ j, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.L.U j)} (hV : SpansFibre L y V θ₀) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.L.U j →
      fr j z * a⁻¹ * θ z = valAt' (e z) (G.hom ⁻¹ᵁ V ⊓ L.L.U j) (θ₀ j) := by
  obtain ⟨-, h2, -, -, s, hs⟩ := h
  obtain ⟨a, ha⟩ := hV s
  have key : ∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.L.U j → θ z * fr j z = a * valAt' (e z) (G.hom ⁻¹ᵁ V ⊓ L.L.U j) (θ₀ j) := by
    intro j z hz
    let x : Sp ℂ ⟶ pullback G.hom y := pullback.lift (e z) (𝟙 _) ((he z).trans (Category.id_comp _).symm)
    have h₁ : x ≫ pullback.fst _ _ = e z := pullback.lift_fst _ _ _
    have h₂ : x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    rw [← hs j z x h₁ h₂ hz, ha j x h₂ (by rw [h₁]; exact hz), h₁]
  have a0 : a ≠ 0 := fun h0 => hθ (funext fun z => by
    obtain ⟨j, hj⟩ := exists_chart_point L (e z)
    have e := key j z hj
    rw [h0, zero_mul] at e
    exact (mul_eq_zero.1 e).resolve_right (h2 j z hj))
  refine ⟨a, a0, fun j z hz => ?_⟩
  rw [mul_right_comm, mul_comm (fr j z), key j z hz]
  field_simp

end Fibre

section Family

variable {B : Set (Fin m → ℂ)} {y : (Fin m → ℂ) → (Sp ℂ ⟶ S)} {e : (Fin m → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G.left)}
  {θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ}

theorem mem_chart_iff {x : Sp ℂ ⟶ G.left} {u : Sp ℂ ⟶ S} (h : x ≫ G.hom = u) (V : S.Opens) (U : G.left.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (G.hom ⁻¹ᵁ V ⊓ U) ↔ ⊤ ≤ u ⁻¹ᵁ V ∧ ⊤ ≤ x ⁻¹ᵁ U := by
  rw [top_le_preimage_inf, ← top_le_preimage_comp, h]

theorem exists_fibreFrame_of_mem_closure (he : ∀ b ∈ B, ∀ z, e b z ≫ G.hom = y b)
    (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => e bz.1 bz.2))
    (hd : DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => θ bz.1 bz.2) (B ×ˢ Set.univ))
    (hnz : ∀ b ∈ B, ∀ z, ∃ᶠ w in 𝓝 z, θ b w ≠ 0) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) {V : S.Opens}
    {θ₀ : ∀ j, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.L.U j)} (hV₀ : ⊤ ≤ y b₀ ⁻¹ᵁ V)
    (hV : ∀ b ∈ B, ⊤ ≤ y b ⁻¹ᵁ V → SpansFibre L (y b) V θ₀)
    {T : Set (Fin m → ℂ)} (hT : ∀ b ∈ T, ∃ fr, IsFibreFrame L (y b) (e b) (θ b) fr) (hcl : b₀ ∈ closure T)
    {θ' : (Fin g → ℂ) → ℂ} (hnz' : ∀ z, ∃ᶠ w in 𝓝 z, θ' w ≠ 0) {fr' : L.L.ι → (Fin g → ℂ) → ℂ}
    (h' : IsFibreFrame L (y b₀) (e b₀) θ' fr') : ∃ fr, IsFibreFrame L (y b₀) (e b₀) (θ b₀) fr := by
  have ne : ∀ {f : (Fin g → ℂ) → ℂ}, (∀ z, ∃ᶠ w in 𝓝 z, f w ≠ 0) → f ≠ 0 := fun h h0 =>
    (h 0).exists.elim fun w hw => hw (congrFun h0 w)
  obtain ⟨a', ha', hr'⟩ := h'.ratio (he b₀ hb₀) (ne hnz') (hV b₀ hb₀ hV₀)
  suffices hloc : ∀ z, ∃ ρ : (Fin g → ℂ) → ℂ, ρ z ≠ 0 ∧ ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ρ w ∧ ρ w * θ' w = θ b₀ w by
    obtain ⟨ρ, h1, h2, h3⟩ := exists_entire_quotient hnz' hloc
    exact ⟨_, h'.rescale h1 h2 h3⟩
  intro z₀
  obtain ⟨j, hj⟩ := exists_chart_point L (e b₀ z₀)
  obtain ⟨hW, hf⟩ := hol (G.hom ⁻¹ᵁ V ⊓ L.L.U j) (θ₀ j)
  set W := {bz ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e bz.1 bz.2 ⁻¹ᵁ (G.hom ⁻¹ᵁ V ⊓ L.L.U j)} with hWd
  have mW : ∀ b z, (b, z) ∈ W → b ∈ B ∧ ⊤ ≤ y b ⁻¹ᵁ V ∧ ⊤ ≤ e b z ⁻¹ᵁ L.L.U j := fun b z h =>
    ⟨h.1.1, (mem_chart_iff (he b h.1.1 z) _ _).1 h.2⟩
  have hw : (b₀, z₀) ∈ W := ⟨⟨hb₀, trivial⟩, (mem_chart_iff (he b₀ hb₀ z₀) _ _).2 ⟨hV₀, hj⟩⟩
  have hθW := hd.mono (fun bz h => h.1 : W ⊆ B ×ˢ Set.univ)
  have hS : ∀ b ∈ T, ∃ F : (Fin g → ℂ) → ℂ, DifferentiableOn ℂ F {z | (b, z) ∈ W} ∧ ∀ z, (b, z) ∈ W →
      F z ≠ 0 ∧ F z * θ b z = valAt' (e b z) (G.hom ⁻¹ᵁ V ⊓ L.L.U j) (θ₀ j) := by
    intro b hb
    by_cases hm : b ∈ B ∧ ⊤ ≤ y b ⁻¹ᵁ V
    · obtain ⟨fr, h⟩ := hT b hb
      obtain ⟨a, ha, hr⟩ := h.ratio (he b hm.1) (ne (hnz b hm.1)) (hV b hm.1 hm.2)
      exact ⟨fun z => fr j z * a⁻¹, ((h.1 j).mono fun z hz => (mW b z hz).2.2).mul_const _, fun z hz =>
        ⟨mul_ne_zero (h.2.1 j z (mW b z hz).2.2) (inv_ne_zero ha), hr j z (mW b z hz).2.2⟩⟩
    · exact ⟨0, differentiableOn_const _, fun z hz => absurd ⟨(mW b z hz).1, (mW b z hz).2.1⟩ hm⟩
  have hc : Continuous fun z : Fin g → ℂ => (b₀, z) := by fun_prop
  have hWz : ∀ᶠ z in 𝓝 z₀, (b₀, z) ∈ W := hc.continuousAt.eventually (hW.mem_nhds hw)
  obtain ⟨U₁, G₁, o₁, w₁, -, d₁, q₁⟩ := exists_quotient_closure hW hf hθW (S := T)
    (fun b hb => (hS b hb).imp fun F h => ⟨h.1, fun z hz => (h.2 z hz).2⟩) hw (hnz b₀ hb₀ z₀)
  obtain ⟨U₂, G₂, o₂, w₂, -, d₂, q₂⟩ := exists_quotient_closure hW hθW hf (S := T)
    (fun b hb => (hS b hb).elim fun F h => ⟨fun z => (F z)⁻¹, h.1.inv fun z hz => (h.2 z hz).1, fun z hz => by
      rw [← (h.2 z hz).2, inv_mul_cancel_left₀ (h.2 z hz).1]⟩) hw
    (((hnz' z₀).and_eventually hWz).mono fun z hz => by
      have := (mW _ _ hz.2).2.2
      rw [← hr' j z this]
      exact mul_ne_zero (mul_ne_zero (h'.2.1 j z this) (inv_ne_zero ha')) hz.1)
  have e₁ : ∀ᶠ z in 𝓝 z₀, (b₀, z) ∈ U₁ := hc.continuousAt.eventually (o₁.mem_nhds w₁)
  have e₂ : ∀ᶠ z in 𝓝 z₀, (b₀, z) ∈ U₂ := hc.continuousAt.eventually (o₂.mem_nhds w₂)
  have hι : Differentiable ℂ fun z : Fin g → ℂ => (b₀, z) := by fun_prop
  have s₁ : DifferentiableAt ℂ (fun z => G₁ (b₀, z)) z₀ := (d₁.differentiableAt (o₁.mem_nhds w₁)).comp z₀ (hι z₀)
  have s₂ : ∀ z, (b₀, z) ∈ U₂ → DifferentiableAt ℂ (fun z => G₂ (b₀, z)) z := fun z hz =>
    (d₂.differentiableAt (o₂.mem_nhds hz)).comp z (hι z)
  have one : G₂ (b₀, z₀) * G₁ (b₀, z₀) = 1 := by
    refine tendsto_nhds_unique_of_frequently_eq ((s₂ z₀ w₂).mul s₁).continuousAt tendsto_const_nhds
      (((hnz b₀ hb₀ z₀).and_eventually (e₁.and e₂)).mono fun z hz => mul_right_cancel₀ hz.1 ?_)
    have p₁ := q₁ _ hz.2.1 hcl
    have p₂ := q₂ _ hz.2.2 hcl
    simp only [Pi.mul_apply] at p₁ p₂ ⊢
    rw [_root_.mul_assoc, p₁, p₂, _root_.one_mul]
  refine ⟨fun z => G₂ (b₀, z) * (fr' j z * a'⁻¹),
    mul_ne_zero (left_ne_zero_of_mul_eq_one one) (mul_ne_zero (h'.2.1 j z₀ hj) (inv_ne_zero ha')), ?_⟩
  filter_upwards [e₂, hWz.eventually_nhds] with z hz hz'
  refine ⟨(s₂ z hz).mul (((h'.1 j).differentiableAt (hz'.mono fun w hw => (mW _ _ hw).2.2)).mul_const _), ?_⟩
  rw [_root_.mul_assoc, hr' j z (mW _ _ hz'.self_of_nhds).2.2]
  exact q₂ _ hz hcl

theorem isThetaFrame_of_fibreFrames (he : ∀ b ∈ B, ∀ z, e b z ≫ G.hom = y b) (he0 : ∀ b ∈ B, e b 0 = y b ≫ eSec G)
    (holy : IsHolTo B y) (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => e bz.1 bz.2))
    (hd : DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => θ bz.1 bz.2) (B ×ˢ Set.univ))
    (hnz : ∀ b ∈ B, ∀ z, ∃ᶠ w in 𝓝 z, θ b w ≠ 0)
    (hsec : ∀ b₀ ∈ B, ∃ (V : S.Opens) (θ₀ : ∀ j, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.L.U j)), ⊤ ≤ y b₀ ⁻¹ᵁ V ∧
      ∀ b ∈ B, ⊤ ≤ y b ⁻¹ᵁ V → SpansFibre L (y b) V θ₀)
    (hT : ∀ b ∈ B, ∃ fr, IsFibreFrame L (y b) (e b) (θ b) fr) : IsThetaFrame L B y e θ := by
  choose! fr hfr using hT
  refine ⟨fun j bz => fr bz.1 j bz.2, fun j w hw => ?_, fun j b z hb => (hfr b hb).2.1 j z,
    fun j j' b z hb => (hfr b hb).2.2.1 j j' z, fun j b hb => (hfr b hb).2.2.2.1 j, fun b hb => (hfr b hb).2.2.2.2⟩
  obtain ⟨b₀, z₀⟩ := w
  obtain ⟨hb₀, hj⟩ : b₀ ∈ B ∧ ⊤ ≤ e b₀ z₀ ⁻¹ᵁ L.L.U j := hw
  obtain ⟨V, θ₀, hV₀, hV⟩ := hsec b₀ hb₀
  have ex : ∀ b, b ∈ B ∧ ⊤ ≤ y b ⁻¹ᵁ V → ∃ a : ℂ, a ≠ 0 ∧ ∀ j z, ⊤ ≤ e b z ⁻¹ᵁ L.L.U j →
      fr b j z * a⁻¹ * θ b z = valAt' (e b z) (G.hom ⁻¹ᵁ V ⊓ L.L.U j) (θ₀ j) := fun b hb =>
    (hfr b hb.1).ratio (he b hb.1) (fun h0 => (hnz b hb.1 0).exists.elim fun w hw => hw (congrFun h0 w)) (hV b hb.1 hb.2)
  choose! a ha hr using ex
  have hF : ∀ k z, ⊤ ≤ e b₀ z ⁻¹ᵁ L.L.U k →
      DifferentiableAt ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => fr bz.1 k bz.2 * (a bz.1)⁻¹) (b₀, z) := by
    intro k z hk
    obtain ⟨hW, hf⟩ := hol (G.hom ⁻¹ᵁ V ⊓ L.L.U k) (θ₀ k)
    set W := {bz ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e bz.1 bz.2 ⁻¹ᵁ (G.hom ⁻¹ᵁ V ⊓ L.L.U k)} with hWd
    have mW : ∀ b z, (b, z) ∈ W → (b ∈ B ∧ ⊤ ≤ y b ⁻¹ᵁ V) ∧ ⊤ ≤ e b z ⁻¹ᵁ L.L.U k := fun b z h =>
      and_assoc.2 ⟨h.1.1, (mem_chart_iff (he b h.1.1 z) _ _).1 h.2⟩
    have hw : (b₀, z) ∈ W := ⟨⟨hb₀, trivial⟩, (mem_chart_iff (he b₀ hb₀ z) _ _).2 ⟨hV₀, hk⟩⟩
    refine (differentiableOn_quotient_of_differentiableOn_slice _ _ W _ _ _ hW hf (hd.mono fun bz h => h.1)
      (fun w hw => hr _ (mW _ _ hw).1 k _ (mW _ _ hw).2) (fun b => ?_)
      (fun w hw => hnz _ hw.1.1 _)).differentiableAt (hW.mem_nhds hw)
    by_cases hb : b ∈ B
    · exact (((hfr b hb).1 k).mono fun z hz => (mW b z hz).2).mul_const (a b)⁻¹
    · exact fun z hz => absurd hz.1.1 hb
  obtain ⟨k, hk⟩ := exists_chart_point L (e b₀ 0)
  obtain ⟨hO, hρ⟩ := holy ((L.L.pull (eSec G)).U (fun _ => k)) (L.rig.s (fun _ => k)).val
  have mO : ∀ b ∈ B, ⊤ ≤ y b ⁻¹ᵁ ((L.L.pull (eSec G)).U (fun _ => k)) ↔ ⊤ ≤ e b 0 ⁻¹ᵁ L.L.U k := fun b hb => by
    rw [he0 b hb, top_le_preimage_iff_mem, top_le_preimage_iff_mem]
    exact mem_pull
  have nO := hO.mem_nhds (⟨hb₀, (mO b₀ hb₀).2 hk⟩ : b₀ ∈ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ ((L.L.pull (eSec G)).U (fun _ => k))})
  have nV := (holy V 0).1.mem_nhds (⟨hb₀, hV₀⟩ : b₀ ∈ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ V})
  have hι : Differentiable ℂ fun b : Fin m → ℂ => (b, (0 : Fin g → ℂ)) := by fun_prop
  have d0 : DifferentiableAt ℂ (fun b => fr b k 0 * (a b)⁻¹) b₀ :=
    DifferentiableAt.comp (f := fun b : Fin m → ℂ => (b, (0 : Fin g → ℂ))) b₀ (hF k 0 hk) (hι b₀)
  have da : DifferentiableAt ℂ a b₀ := by
    refine ((hρ.differentiableAt nO).mul (d0.inv (mul_ne_zero ((hfr b₀ hb₀).2.1 k 0 hk)
      (inv_ne_zero (ha b₀ ⟨hb₀, hV₀⟩))))).congr_of_eventuallyEq ?_
    filter_upwards [nO, nV] with b h1 h2
    have h3 := (mO b h1.1).1 h1.2
    have h4 := (hfr b h1.1).2.1 k 0 h3
    have h5 := ha b h2
    refine Eq.trans ?_ (congrArg (· * (fr b k 0 * (a b)⁻¹)⁻¹) ((hfr b h1.1).2.2.2.1 k h3))
    field_simp
  refine (((hF j z₀ hj).mul (da.comp (b₀, z₀) differentiableAt_fst)).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [(continuous_fst.continuousAt (x := (b₀, z₀))).preimage_mem_nhds nV] with bz h
  exact (inv_mul_cancel_right₀ (ha _ h) _).symm

end Family

end GlobalTheory.ThetaFamily
