import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.TranslInv
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.BezoutHypotheses.Bez2
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.NilpotentHypotheses.ContinuousLin

noncomputable section

open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.TP.Nil.Asm

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil

section Lemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem continuous_hom (t : kˣ) : Continuous (hom (n := n) t) := by
  unfold hom
  fun_prop

theorem hom_hom_inv (t : kˣ) (p : Sp k n) : hom t (hom t⁻¹ p) = p := by
  simp [hom, smul_smul]

theorem hom_inv_hom (t : kˣ) (p : Sp k n) : hom t⁻¹ (hom t p) = p := by
  simp [hom, smul_smul]

def homH (t : kˣ) : Sp k n ≃ₜ Sp k n where
  toFun := hom t
  invFun := hom t⁻¹
  left_inv := hom_inv_hom t
  right_inv := hom_hom_inv t
  continuous_toFun := continuous_hom t
  continuous_invFun := continuous_hom t⁻¹

theorem comp_hom_mem (t : kˣ) {f : Sp k n → ℂ} (hf : f ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ) :
    f ∘ hom t ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ := by
  obtain ⟨hlc, hcs⟩ := hf
  exact ⟨hlc.comp_continuous (continuous_hom t), hcs.comp_homeomorph (homH t)⟩

theorem pullH_apply (t : kˣ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) (f : Sp k n → ℂ) : pullH t ξ f = ξ (f ∘ hom t) := rfl

theorem pullH_supp {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (t : kˣ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ)
    (h : Supp ξ (Bz Z ×ˢ Set.univ)) : Supp (pullH t ξ) (Bz Z ×ˢ Set.univ) := by
  intro f hf h0
  rw [pullH_apply]
  refine h _ ⟨comp_hom_mem t hf.1, Set.subset_univ _⟩ ?_
  rintro ⟨x, v⟩ ⟨hx, -⟩
  show f (hom t (x, v)) = 0
  apply h0
  refine ⟨?_, Set.mem_univ _⟩
  intro a ha
  show a * ((t : k) • x) = ((t : k) • x) * a
  rw [mul_smul_comm, smul_mul_assoc, hx a ha]

theorem pullH_inv (t : kˣ) :
    pullH (n := n) t ∘ₗ pullH t⁻¹ = LinearMap.id ∧ pullH (n := n) t⁻¹ ∘ₗ pullH t = LinearMap.id := by
  refine ⟨LinearMap.ext fun ξ => LinearMap.ext fun f => ?_, LinearMap.ext fun ξ => LinearMap.ext fun f => ?_⟩
  · show ξ ((f ∘ hom t) ∘ hom t⁻¹) = ξ f
    congr 1; funext p; simp [hom_hom_inv]
  · show ξ ((f ∘ hom t⁻¹) ∘ hom t) = ξ f
    congr 1; funext p; simp [hom_inv_hom]

theorem pullH_kills (t : kˣ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) (h : Kills ξ UU) : Kills (pullH t ξ) UU := by
  intro f hf
  rw [pullH_apply]
  refine h _ ⟨comp_hom_mem t hf.1, fun p hp => ?_⟩
  have := hf.2 hp
  simpa [UU, hom] using this

def Bo (t : kˣ) (x : ℝ) : Module.End ℂ ((Sp k n → ℂ) →ₗ[ℂ] ℂ) :=
  pullH t - (((((nabs k t)⁻¹ : ℝ) ^ x : ℝ)) : ℂ) • LinearMap.id

def Ao (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (t : kˣ) (x : ℝ) : Module.End ℂ ((Sp k n → ℂ) →ₗ[ℂ] ℂ) :=
  ((((nabs k t)⁻¹ ^ dB Z : ℝ)) : ℂ) • pullH t⁻¹ - (((((nabs k t)⁻¹ : ℝ) ^ x : ℝ)) : ℂ) • LinearMap.id

def Agr (η η' : (Sp k n → ℂ) →ₗ[ℂ] ℂ) : Prop := ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), η f = η' f

theorem ao_agree (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (t : kˣ) (x : ℝ) {η η' : (Sp k n → ℂ) →ₗ[ℂ] ℂ}
    (h : Agr η η') : Agr (Ao Z t x η) (Ao Z t x η') := by
  intro f hf
  simp only [Ao, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, pullH_apply]
  rw [h f hf, h _ ⟨comp_hom_mem t⁻¹ hf.1, Set.subset_univ _⟩]

theorem polyH_eq (t : kˣ) (a : List ℝ) : polyH (n := n) t a = (a.map (Bo t)).prod := rfl

theorem bo_supp {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (t : kˣ) (a : List ℝ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ)
    (hξ : Supp ξ (Bz Z ×ˢ Set.univ)) : Supp ((a.map (Bo t)).prod ξ) (Bz Z ×ˢ Set.univ) := by
  induction a with
  | nil => simpa using hξ
  | cons x a ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    intro f hf h0
    simp only [Bo, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [pullH_supp t _ ih f hf h0, ih f hf h0, smul_zero, sub_zero]

theorem four_prodH {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}
    (𝓕 : ((Sp k n → ℂ) →ₗ[ℂ] ℂ) →ₗ[ℂ] ((Sp k n → ℂ) →ₗ[ℂ] ℂ))
    (hF5 : ∀ (t : kˣ) ξ, Supp ξ (Bz Z ×ˢ Set.univ) → ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)),
        𝓕 (pullH t ξ) f = ((((nabs k t)⁻¹ ^ dB Z : ℝ)) : ℂ) * pullH t⁻¹ (𝓕 ξ) f)
    (t : kˣ) (a : List ℝ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) (hξ : Supp ξ (Bz Z ×ˢ Set.univ)) :
    Agr (𝓕 ((a.map (Bo t)).prod ξ)) ((a.map (Ao Z t)).prod (𝓕 ξ)) := by
  induction a with
  | nil =>
    intro f hf
    simp
  | cons x a ih =>
    have hP := bo_supp t a ξ hξ
    have h1 := ao_agree Z t x ih
    intro f hf
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.map_cons, List.prod_cons,
      Module.End.mul_apply, ← h1 f hf]
    simp only [Bo, Ao, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
      map_smul]
    rw [hF5 t _ hP f hf]
    simp only [smul_eq_mul]

theorem dZ_le (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) : Module.finrank k Z ≤ dB Z := by
  have hle : Subalgebra.toSubmodule Z ≤
      Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) := by
    intro a ha
    show a ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))
    rw [Subalgebra.mem_centralizer_iff]
    intro b hb
    exact hZ.1 b hb a ha
  exact Submodule.finrank_mono hle

theorem suppU_of_H {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (η : (Sp k n → ℂ) →ₗ[ℂ] ℂ)
    (hH : ∀ U : Set (Sp k n), IsOpen U → (∀ p ∈ U, p.2 ≠ 0 ∧ p.1 ∉ ZN Z ∩ Bz Z) → Kills η U) :
    SuppU η ((ZN Z ∩ Bz Z) ×ˢ Set.univ) := by
  intro f hf h0
  obtain ⟨⟨hlc, hcs⟩, hsu⟩ := hf
  have hopen : IsOpen (Function.support f) := (hlc.isClosed_fiber 0).isOpen_compl
  exact hH _ hopen (fun p hp => ⟨hsu hp, fun hmem => hp (h0 p ⟨hmem, Set.mem_univ _⟩)⟩) f
    ⟨⟨hlc, hcs⟩, subset_rfl⟩

end Lemmas

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nilCore_of : FourQ k → OrbQ k → FibQ k → BaseQ k → TraceForm k →
    PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) → NilCore k := by
  intro hF hO hFi hBa hT hU m Z hZ H ξ hξ hinv
  rcases Nat.eq_zero_or_pos (dB0 Z) with h0 | hpos
  · exact hBa m Z hZ h0 ξ hξ hinv
  obtain ⟨t, -, ht⟩ := PositivityTheory.RgUd.T.Nil.Asm.free_etale_sheaf_zmod_exists_hom_sending_generator k
  obtain ⟨𝓕, hF1, hF2, hF3, -, hF5, hF6⟩ := hF hT m Z hZ
  obtain ⟨a, ha, hOa⟩ := hO hT hU m Z hZ hpos t ht
  have hξB : Supp ξ (Bz Z ×ˢ Set.univ) := fun f hf h0 =>
    hξ f hf (fun p hp => h0 p ⟨hp.1.1, hp.2⟩)
  have hη1 := hF1 ξ hξB
  have hη2 := hF2 ξ hξB hinv
  have hη6 := hF6 ξ hξ
  have hηU := suppU_of_H (𝓕 ξ) (H (𝓕 ξ) hη1 hη2)
  obtain ⟨η', hη'S, hη'I, hη'K⟩ := hFi m Z hZ (𝓕 ξ) hη1 hη2 hη6 hηU
  have hb := hη'K t ht a (hOa η' hη'S hη'I)
  have hξU : SuppU ξ (NB Z ×ˢ Set.univ) := fun f hf h0 => hξ f ⟨hf.1, Set.subset_univ _⟩ h0
  have hξI : InvU Z ξ := fun g hg f hf => hinv g hg f ⟨hf.1, Set.subset_univ _⟩
  have ha2 : Kills (polyH t a ξ) UU := hOa ξ hξU hξI
  rw [polyH_eq] at ha2
  have ha3 : Kills ((a.map (Ao Z t)).prod (𝓕 ξ)) UU := by
    have hk := (hF3 _ (bo_supp t a ξ hξB)).mp ha2
    have hag := four_prodH 𝓕 hF5 t a ξ hξB
    intro f hf
    rw [← hag f ⟨hf.1, Set.subset_univ _⟩]
    exact hk f hf
  have hpos' : 0 < nabs k t := GlobalTheory.SplitWeil.nabs_pos k t
  have hc1 : 1 < (nabs k t)⁻¹ := (one_lt_inv₀ hpos').mpr ht
  let K : Submodule ℂ ((Sp k m → ℂ) →ₗ[ℂ] ℂ) :=
    { carrier := {η | Kills η UU}
      add_mem' := by
        intro x y hx hy f hf
        have h1 : x f = 0 := hx f hf
        have h2 : y f = 0 := hy f hf
        simp [h1, h2]
      zero_mem' := by
        intro f _
        simp
      smul_mem' := by
        intro c x hx f hf
        have h1 : x f = 0 := hx f hf
        simp [h1] }
  have hmain : 𝓕 ξ ∈ K := by
    refine bez2 K (pullH t) (pullH t⁻¹) (pullH_inv t).1 (pullH_inv t).2
      (fun η hη => pullH_kills t η hη) (nabs k t)⁻¹ hc1 (dB Z : ℝ) a
      (a.map (fun x => x + (Module.finrank k Z : ℝ))) ?_ (𝓕 ξ) hb ?_
    · intro x hx y hy
      obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hy
      have h1 := ha x hx
      have h2 := ha x' hx'
      have hle := dZ_le Z hZ
      have hd : (dB0 Z : ℝ) = (dB Z : ℝ) - (Module.finrank k Z : ℝ) := by
        rw [show dB0 Z = dB Z - Module.finrank k Z from rfl, Nat.cast_sub hle]
      apply ne_of_lt
      linarith
    · have e : ∀ x : ℝ, ((((nabs k t)⁻¹ ^ (dB Z : ℝ) : ℝ)) : ℂ) • pullH t⁻¹ -
          ((((nabs k t)⁻¹ ^ x : ℝ)) : ℂ) • LinearMap.id = Ao Z t x := by
        intro x
        simp only [Ao, Real.rpow_natCast]
      simp only [e]
      exact ha3
  exact (hF3 ξ hξB).mpr hmain

end PositivityTheory.RgUd.TP.Nil.Asm
