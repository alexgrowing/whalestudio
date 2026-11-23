import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfIsPlaceOver

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
open scoped commutatorElement

namespace UpperTheory.GalS

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem mem_of_gen {n : ℕ} {a : WDRep h (Fin n → ℂ)} (ha : a.Tame) {γ : G E Ω} (hγ : TameGenAt A γ)
    (S : Subgroup (End ℂ (Fin n → ℂ))ˣ) (h1 : a.ρ.toHomUnits (ineIncl h ⟨γ, hγ.1⟩) ∈ S) (σ : Ine (F := E) A) :
    a.ρ.toHomUnits (ineIncl h σ) ∈ S := by
  let K : Subgroup (Ine (F := E) A) := S.comap (a.ρ.toHomUnits.comp (ineIncl h))
  have one : ∀ τ : Ine (F := E) A, a.ρ (ineIncl h τ) = 1 → τ ∈ K := fun τ e => by
    have : a.ρ.toHomUnits (ineIncl h τ) = 1 := Units.ext e
    show a.ρ.toHomUnits (ineIncl h τ) ∈ S
    rw [this]; exact S.one_mem
  have hO : IsOpen (K : Set (Ine (F := E) A)) :=
    Subgroup.isOpen_mono (H₁ := (a.ρ.comp (ineIncl h)).ker) (fun τ e => one τ e) a.smooth
  have hK : IsClosed ((K.map (Ine (F := E) A).subtype : Subgroup (G E Ω)) : Set (G E Ω)) :=
    (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ (K.isClosed_of_isOpen hO)
  have hle : Subgroup.closure (insert γ (Wild E A : Set (G E Ω))) ≤ K.map (Ine (F := E) A).subtype := by
    rw [Subgroup.closure_le]
    rintro u (rfl | hu)
    · exact ⟨⟨u, hγ.1⟩, h1, rfl⟩
    · exact ⟨⟨u, Wild_le_Ine hu⟩, one _ (ha _ hu), rfl⟩
  obtain ⟨u, hu, e⟩ := closure_minimal (SetLike.coe_subset_coe.mpr hle) hK (hγ.2 σ.2)
  rwa [← Subtype.ext (a1 := u) (a2 := σ) e]

theorem pow_eq_one_of_roots {n : ℕ} {f : End ℂ (Fin n → ℂ)} (hf : f.IsSemisimple) {m : ℕ}
    (k : ∀ z : ℂ, f.charpoly.IsRoot z → z ^ m = 1) : f ^ m = 1 := by
  have top := hf.iSup_eigenspace_eq_top
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ ⨆ z, f.eigenspace z := top ▸ Submodule.mem_top
  induction hv using Submodule.iSup_induction' with
  | mem z x hx =>
    by_cases h0 : x = 0
    · simp [h0]
    · have he : f.HasEigenvector z x := ⟨hx, h0⟩
      rw [he.pow_apply, k z ((End.hasEigenvalue_iff_isRoot_charpoly _ _).1 (End.hasEigenvalue_of_hasEigenvector he))]
      simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]

theorem tor_of_ncW {y : WD h} (ht : thr w y.lpDim = 1) (k : NcW y) : UpperTheory.GalStar.Tor y := by
  obtain ⟨n, a, rfl⟩ := y.exists_rep
  have ha : a.Tame := (WD.tame_mk a).1 ((WD.tame_iff_inePol _).2 fun σ hσ => k.1 σ hσ)
  obtain ⟨γ, hγ⟩ : ∃ γ : G E Ω, TameGenAt A γ := GlobalTheory.exists_tameGenAt_of_isPlaceOver E Ω A w h
  let u := a.ρ.toHomUnits
  let g : Weil h := ineIncl h ⟨γ, hγ.1⟩
  have hq : 1 ≤ normV w := Nat.pos_of_ne_zero fun h0 => by
    have : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
    exact (Nat.card_pos (α := 𝓞 E ⧸ w.asIdeal)).ne' h0
  have p1 : a.ρ g ^ (normV w - 1) = 1 := pow_eq_one_of_roots (a.semisimple g) fun z hz => by
    refine k.2.2 γ hγ.1 hγ.2 z ?_
    rw [ht, WD.inePol_of_mem_Ine _ hγ.1, WD.charPol_mk]
    exact (rootMultiplicity_pos (LinearMap.charpoly_monic _).ne_zero).2 hz
  have p2 : a.ρ (frob h * g * (frob h)⁻¹) = a.ρ g := by
    rw [ha.conj_eq_pow hγ.1 deg_frob, ← Nat.sub_add_cancel hq, pow_succ, p1, one_mul]
  have c1 : Commute (u (frob h)) (u g) := by
    have e : u (frob h * g * (frob h)⁻¹) = u g := Units.ext p2
    rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul] at e
    exact e
  have cen : ∀ x : (End ℂ (Fin n → ℂ))ˣ, Commute x (u g) → ∀ σ, Commute x (u (ineIncl h σ)) := fun x hx σ =>
    Subgroup.mem_centralizer_singleton_iff.1
      (mem_of_gen ha hγ (Subgroup.centralizer {x}) (Subgroup.mem_centralizer_singleton_iff.2 hx.symm) σ) |>.symm
  have c2 := cen _ c1
  have c3 : ∀ τ σ, Commute (u (ineIncl h τ)) (u (ineIncl h σ)) := fun τ => cen _ (cen _ (Commute.refl _) τ).symm
  intro s t
  have c : Commute (u s) (u t) := by
    obtain ⟨τ, e⟩ := exists_eq_zpow_mul deg_frob s
    obtain ⟨τ', e'⟩ := exists_eq_zpow_mul deg_frob t
    rw [e, e', map_mul, map_mul, map_zpow, map_zpow]
    exact Commute.mul_left (Commute.mul_right (Commute.zpow_zpow_self _ _ _) ((c2 τ').zpow_left _))
      (Commute.mul_right ((c2 τ).symm.zpow_right _) (c3 τ τ'))
  have e : a.ρ ⁅s, t⁆ = 1 := by
    have := (map_commutatorElement u s t).trans (commutatorElement_eq_one_iff_commute.2 c)
    exact congrArg Units.val this
  show (WD.mk a).charPol _ = _
  rw [WD.charPol_mk, e, LinearMap.charpoly_one, WD.lpDim_mk]

end UpperTheory.GalS
