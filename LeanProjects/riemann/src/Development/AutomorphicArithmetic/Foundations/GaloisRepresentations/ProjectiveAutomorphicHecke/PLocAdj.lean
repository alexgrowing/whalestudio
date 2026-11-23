import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap.LocalAdjunction

variable {C V : Type} [Group C] [AddCommGroup V] [Module ℂ V]

private structure Lvl (χ : C →* ℂˣ) where
  N : Subgroup C
  nrm : N.Normal
  fin : N.FiniteIndex
  triv : ∀ n ∈ N, χ n = 1

attribute [instance] Lvl.nrm Lvl.fin

private noncomputable instance {χ : C →* ℂˣ} (L : Lvl χ) : Fintype (C ⧸ L.N) := Fintype.ofFinite _

private noncomputable def Lvl.ofFI {χ : C →* ℂˣ} (N : Subgroup C) (hN : N.FiniteIndex) (h : ∀ n ∈ N, χ n = 1) : Lvl χ :=
  ⟨N.normalCore, inferInstance, inferInstance, fun n hn => h n (Subgroup.normalCore_le N hn)⟩

private theorem Lvl.ofFI_le {χ : C →* ℂˣ} (N : Subgroup C) (hN : N.FiniteIndex) (h : ∀ n ∈ N, χ n = 1) :
    (Lvl.ofFI N hN h).N ≤ N := Subgroup.normalCore_le N

private def Lvl.inf {χ : C →* ℂˣ} (L L' : Lvl χ) : Lvl χ :=
  ⟨L.N ⊓ L'.N, inferInstance, inferInstance, fun n hn => L.triv n hn.1⟩

private def Fx (σ : Representation ℂ C V) (N : Subgroup C) (x : V) : Prop := ∀ n ∈ N, σ n x = x

private theorem Fx.mono {σ : Representation ℂ C V} {N N' : Subgroup C} {x : V} (h : Fx σ N x) (hle : N' ≤ N) : Fx σ N' x :=
  fun n hn => h n (hle hn)

private noncomputable def tw (σ : Representation ℂ C V) (χ : C →* ℂˣ) (x : V) (k : C) : V := ((χ k : ℂˣ) : ℂ)⁻¹ • σ k x

private noncomputable def av (σ : Representation ℂ C V) (χ : C →* ℂˣ) (L : Lvl χ) : V →ₗ[ℂ] V :=
  (Nat.card (C ⧸ L.N) : ℂ)⁻¹ • ∑ q : C ⧸ L.N, ((χ q.out : ℂˣ) : ℂ)⁻¹ • σ q.out

variable {σ : Representation ℂ C V} {χ : C →* ℂˣ}

private theorem av_apply (L : Lvl χ) (x : V) :
    av σ χ L x = (Nat.card (C ⧸ L.N) : ℂ)⁻¹ • ∑ q : C ⧸ L.N, tw σ χ x q.out := by
  simp [av, tw, LinearMap.sum_apply]

private theorem card_ne (L : Lvl χ) : (Nat.card (C ⧸ L.N) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 Nat.card_pos.ne'

private theorem tw_congr (L : Lvl χ) {x : V} (hx : Fx σ L.N x) {a b : C} (h : (a : C ⧸ L.N) = b) :
    tw σ χ x a = tw σ χ x b := by
  have hn : a⁻¹ * b ∈ L.N := QuotientGroup.eq.1 h
  have hb : b = a * (a⁻¹ * b) := by group
  generalize a⁻¹ * b = n at hn hb
  subst hb
  simp only [tw, map_mul, Module.End.mul_apply, hx n hn, L.triv n hn, mul_one]

private theorem tw_left (x : V) (k a : C) : σ k (tw σ χ x a) = ((χ k : ℂˣ) : ℂ) • tw σ χ x (k * a) := by
  simp only [tw, map_smul, map_mul, Module.End.mul_apply, Units.val_mul, smul_smul]
  congr 1
  have h1 : ((χ k : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have h2 : ((χ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

private theorem tw_right (x : V) (k a : C) : tw σ χ (σ k x) a = ((χ k : ℂˣ) : ℂ) • tw σ χ x (a * k) := by
  simp only [tw, map_mul, Module.End.mul_apply, Units.val_mul, smul_smul]
  congr 1
  have h1 : ((χ k : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have h2 : ((χ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

private theorem av_eig (L : Lvl χ) {x : V} (hx : Fx σ L.N x) (k : C) :
    σ k (av σ χ L x) = ((χ k : ℂˣ) : ℂ) • av σ χ L x := by
  have hs : ∑ q : C ⧸ L.N, tw σ χ x q.out = ∑ q : C ⧸ L.N, tw σ χ x (k * q.out) := by
    rw [← Equiv.sum_comp (Equiv.mulLeft (k : C ⧸ L.N)) (fun q => tw σ χ x q.out)]
    refine Finset.sum_congr rfl fun q _ => tw_congr L hx ?_
    simp
  have e : ∑ q : C ⧸ L.N, σ k (tw σ χ x q.out) = ((χ k : ℂˣ) : ℂ) • ∑ q : C ⧸ L.N, tw σ χ x q.out := by
    rw [hs, Finset.smul_sum]
    exact Finset.sum_congr rfl fun q _ => tw_left x k _
  rw [av_apply, map_smul, map_sum, e, smul_comm]

private theorem av_translate (L : Lvl χ) {x : V} (hx : Fx σ L.N x) (k : C) :
    av σ χ L (σ k x) = ((χ k : ℂˣ) : ℂ) • av σ χ L x := by
  have hs : ∑ q : C ⧸ L.N, tw σ χ x q.out = ∑ q : C ⧸ L.N, tw σ χ x (q.out * k) := by
    rw [← Equiv.sum_comp (Equiv.mulRight (k : C ⧸ L.N)) (fun q => tw σ χ x q.out)]
    refine Finset.sum_congr rfl fun q _ => tw_congr L hx ?_
    simp
  rw [av_apply, av_apply, hs, smul_comm]
  simp only [tw_right, Finset.smul_sum]

private theorem av_of_eig (L : Lvl χ) {y : V} (hy : ∀ k, σ k y = ((χ k : ℂˣ) : ℂ) • y) : av σ χ L y = y := by
  have h : ∀ k, tw σ χ y k = y := fun k => by
    rw [tw, hy k, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
  simp only [av_apply, h, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ]
  rw [smul_smul, inv_mul_cancel₀ (card_ne L), one_smul]

private theorem av_refine {L' L : Lvl χ} (hle : L'.N ≤ L.N) {x : V} (hx : Fx σ L.N x) : av σ χ L' x = av σ χ L x := by
  have h1 : av σ χ L' (av σ χ L x) = av σ χ L x := av_of_eig L' (av_eig L hx)
  have h2 : av σ χ L' (av σ χ L x) = av σ χ L' x := by
    have h : ∀ k, av σ χ L' (tw σ χ x k) = av σ χ L' x := fun k => by
      rw [tw, map_smul, av_translate L' (hx.mono hle), smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
    rw [av_apply L x, map_smul, map_sum]
    simp only [h, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ]
    rw [smul_smul, inv_mul_cancel₀ (card_ne L), one_smul]
  rw [← h2, h1]

private theorem av_indep {L L' : Lvl χ} {x : V} (hx : Fx σ L.N x) (hx' : Fx σ L'.N x) : av σ χ L x = av σ χ L' x :=
  (av_refine (L' := L.inf L') inf_le_left hx).symm.trans (av_refine (L' := L.inf L') inf_le_right hx')

private theorem av_comm (L : Lvl χ) (T : V →ₗ[ℂ] V) (hT : ∀ k x, T (σ k x) = σ k (T x)) (x : V) :
    av σ χ L (T x) = T (av σ χ L x) := by
  simp only [av_apply, map_smul, map_sum, tw, hT]

private def Z (σ : Representation ℂ C V) (χ : C →* ℂˣ) (x : V) : Prop := ∃ L : Lvl χ, Fx σ L.N x ∧ av σ χ L x = 0

private theorem Z.av_eq {x : V} (h : Z σ χ x) {L : Lvl χ} (hx : Fx σ L.N x) : av σ χ L x = 0 := by
  obtain ⟨L', h', h0⟩ := h
  rw [av_indep hx h', h0]

private theorem Z.add {x y : V} (hx : Z σ χ x) (hy : Z σ χ y) : Z σ χ (x + y) := by
  obtain ⟨L, h, h0⟩ := id hx
  obtain ⟨L', h', h0'⟩ := id hy
  have a : Fx σ (L.inf L').N x := h.mono inf_le_left
  have b : Fx σ (L.inf L').N y := h'.mono inf_le_right
  exact ⟨L.inf L', fun n hn => by rw [map_add, a n hn, b n hn], by rw [map_add, hx.av_eq a, hy.av_eq b, add_zero]⟩

private theorem Z.smul {x : V} (hx : Z σ χ x) (a : ℂ) : Z σ χ (a • x) := by
  obtain ⟨L, h, h0⟩ := hx
  exact ⟨L, fun n hn => by rw [map_smul, h n hn], by rw [map_smul, h0, smul_zero]⟩

private theorem exists_lvl {π : Submodule ℂ V} (hsm : ∀ φ ∈ π, ∃ N : Subgroup C, N.FiniteIndex ∧ Fx σ N φ)
    (L₀ : Lvl χ) (s : Finset V) (hs : ∀ x ∈ s, x ∈ π) : ∃ L : Lvl χ, ∀ x ∈ s, Fx σ L.N x := by
  induction s using Finset.induction_on with
  | empty => exact ⟨L₀, by simp⟩
  | insert a s _ ih =>
    obtain ⟨L, hL⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
    obtain ⟨N, hN, hfix⟩ := hsm a (hs a (Finset.mem_insert_self _ _))
    have hfi : (L.N ⊓ N).FiniteIndex := inferInstance
    have hle := Lvl.ofFI_le (χ := χ) (L.N ⊓ N) hfi (fun n hn => L.triv n hn.1)
    refine ⟨Lvl.ofFI (L.N ⊓ N) hfi (fun n hn => L.triv n hn.1), fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hfix.mono (hle.trans inf_le_right)
    · exact (hL x hx).mono (hle.trans inf_le_left)

end UpperTheory.Gal.CertificateRingHomMap.LocalAdjunction

open UpperTheory.Gal.CertificateRingHomMap.LocalAdjunction in
theorem UpperTheory.Gal.CertificateRingHomMap.pLocAdj_of :
    UpperTheory.Gal.CertificateRingHomMap.LocAdj := by
  intro G V X _ _ _ _ _ _ ρ π hinv hirr H C hCH hdec hsm χ ⟨φ₀, hφ₀π, hφ₀, hφ₀χ⟩ f hf hfπ
  let σ : Representation ℂ C V := ρ.comp C.subtype
  have hσ : ∀ (k : C) x, σ k x = ρ (k : G) x := fun _ _ => rfl
  have hsm' : ∀ φ ∈ π, ∃ N : Subgroup C, N.FiniteIndex ∧ Fx σ N φ := hsm
  obtain ⟨N₀, hN₀, hfix₀⟩ := hsm' φ₀ hφ₀π
  have hχ₀ : ∀ n ∈ N₀, χ n = 1 := fun n hn => by
    have h1 : ((χ n : ℂˣ) : ℂ) • φ₀ = (1 : ℂ) • φ₀ := by rw [one_smul, ← hφ₀χ n]; exact hfix₀ n hn
    exact Units.ext (smul_left_injective ℂ hφ₀ h1)
  let L₀ : Lvl χ := Lvl.ofFI N₀ hN₀ hχ₀
  have hfixL₀ : Fx σ L₀.N φ₀ := hfix₀.mono (Lvl.ofFI_le _ _ _)

  let Nn : Submodule ℂ V :=
    { carrier := {φ | φ ∈ π ∧ ∀ h ∈ H, Z σ χ (ρ h φ)}
      zero_mem' := ⟨π.zero_mem, fun h _ => ⟨L₀, fun n _ => by simp, by simp⟩⟩
      add_mem' := fun {a b} ha hb => ⟨π.add_mem ha.1 hb.1, fun h hh => by
        rw [map_add]; exact (ha.2 h hh).add (hb.2 h hh)⟩
      smul_mem' := fun c x hx => ⟨π.smul_mem c hx.1, fun h hh => by
        rw [map_smul]; exact (hx.2 h hh).smul c⟩ }
  have hNn : Nn ≤ π := fun x hx => hx.1
  have hstab : ∀ g, ∀ φ ∈ Nn, ρ g φ ∈ Nn := by
    rintro g φ ⟨hπ, hZ⟩
    obtain ⟨h₁, hh₁, c, hc, rfl⟩ := hdec g
    refine ⟨hinv _ _ hπ, fun h hh => ?_⟩
    obtain ⟨L, hL, h0⟩ := hZ (h * h₁) (H.mul_mem hh hh₁)
    have e : ρ h (ρ (h₁ * c) φ) = ρ c (ρ (h * h₁) φ) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, ← mul_assoc, hc (h * h₁) (H.mul_mem hh hh₁)]
    have hT : ∀ (k : C) x, ρ c (σ k x) = σ k (ρ c x) := fun k x => by
      rw [hσ, hσ, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hc k (hCH k.2)]
    rw [e]
    exact ⟨L, fun n hn => by rw [← hT, hL n hn], by rw [av_comm L (ρ c) hT, h0, map_zero]⟩
  have hφ₀N : φ₀ ∉ Nn := fun h => by
    have h1 := h.2 1 H.one_mem
    rw [map_one, Module.End.one_apply] at h1
    exact hφ₀ ((av_of_eig L₀ hφ₀χ).symm.trans (h1.av_eq hfixL₀))
  have hbot : Nn = ⊥ := by
    rcases hirr Nn hNn hstab with h | h
    · exact h
    · exact absurd (h ▸ hφ₀π) hφ₀N
  obtain ⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hf (LinearMap.ext hh)
  obtain ⟨h, hh, hZ⟩ : ∃ h ∈ H, ¬ Z σ χ (ρ h (f v₀)) := by
    by_contra hcon
    push_neg at hcon
    have : f v₀ ∈ Nn := ⟨hfπ v₀, hcon⟩
    rw [hbot] at this
    exact hv₀ ((Submodule.mem_bot ℂ).1 this)
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℂ X).FG)
  obtain ⟨L, hL⟩ := exists_lvl (σ := σ) hsm' L₀ (s.image fun v => ρ h (f v)) (fun x hx => by
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hx
    exact hinv _ _ (hfπ v))
  have hfix : ∀ v, Fx σ L.N (ρ h (f v)) := fun v n hn => by
    have := LinearMap.ext_on hs (f := (σ n) ∘ₗ (ρ h) ∘ₗ f) (g := (ρ h) ∘ₗ f) (fun v hv =>
      hL _ (Finset.mem_image_of_mem _ hv) n hn)
    exact LinearMap.congr_fun this v
  let r : G →₀ ℂ := ∑ q : C ⧸ L.N, Finsupp.single (((q.out : C) : G) * h)
    ((Nat.card (C ⧸ L.N) : ℂ)⁻¹ * ((χ q.out : ℂˣ) : ℂ)⁻¹)
  have hr : ∀ v, (r.sum fun g a => a • ρ g (f v)) = av σ χ L (ρ h (f v)) := fun v => by
    have e : (r.sum fun g a => a • ρ g (f v)) = Finsupp.linearCombination ℂ (fun g => ρ g (f v)) r :=
      (Finsupp.linearCombination_apply _ _).symm
    rw [e, av_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finsupp.linearCombination_single, map_mul, Module.End.mul_apply, tw, mul_smul]
    rfl
  refine ⟨r, fun g hg => ?_, ⟨v₀, ?_⟩, fun k v => ?_⟩
  · have : r ∈ Finsupp.supported ℂ ℂ (H : Set G) :=
      Submodule.sum_mem _ fun q _ => Finsupp.single_mem_supported ℂ _ (H.mul_mem (hCH q.out.2) hh)
    exact Finsupp.mem_supported _ _ |>.1 this hg
  · rw [hr]
    exact fun h0 => hZ ⟨L, hfix v₀, h0⟩
  · rw [hr]
    exact av_eig L (hfix v) k
