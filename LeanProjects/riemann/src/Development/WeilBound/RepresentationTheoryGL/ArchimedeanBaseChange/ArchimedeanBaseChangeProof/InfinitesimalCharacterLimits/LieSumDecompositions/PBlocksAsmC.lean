import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksAsmB

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))} {c : ℂ}
  {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}

theorem inf_piece {a : ℕ} {X : Submodule ℂ (Sm E a)} {σ : (E →+* ℂ) → Multiset ℂ} {sh : ℂ}
    (mm : (E →+* ℂ) → Multiset ℂ) (hmmN : ∀ τ, (mm τ).Nodup) (hσ : σ ∈ adm mm a)
    (hX : ∀ φ ∈ X, ∀ τ w, cap τ w φ = ((σ τ).map (fun z => w + sh + z)).prod • φ) (τ : E →+* ℂ) :
    HasInfCharGL X τ ((σ τ).map (· + sh)) ∧ ((σ τ).map (· + sh)).Nodup := by
  refine ⟨⟨by rw [Multiset.card_map]; exact (mem_adm.1 hσ τ).2, fun u φ hφ => ?_⟩,
    (Multiset.nodup_of_le (mem_adm.1 hσ τ).1 (hmmN τ)).map (add_left_injective sh)⟩
  rw [hX φ hφ τ u, Multiset.map_map]
  congr 2
  exact Multiset.map_congr rfl fun z _ => by simp only [Function.comp_apply]; ring

theorem hyp_left (hU : IsAutSt U) (hNP : NonPos U) (hT : IsSliceMap U c T) (hpE : pE E (r + s) r c = 0)
    (mm : (E →+* ℂ) → Multiset ℂ) (hmmN : ∀ τ, (mm τ).Nodup) {σ : (E →+* ℂ) → Multiset ℂ} (hσ : σ ∈ adm mm r)
    {z : Module.End ℂ (Sm E r)} (hzc : ∀ o, Commute z (act o))
    (hzE : ∀ φ ∈ LS U T, z φ ∈ Eig (LS U T) σ ((s : ℂ) / 2))
    (hfg : ∃ S₁ : Finset (Sm E r), (↑S₁ : Set (Sm E r)) ⊆ LS U T ∧
      ∀ W : Submodule ℂ (Sm E r), IsStable W → (↑S₁ : Set (Sm E r)) ⊆ W → LS U T ≤ W) (τ : E →+* ℂ) :
    Hyp τ (tw ((LS U T).map z) (-(s : ℂ) / 2)) := by
  have hXle : (LS U T).map z ≤ LS U T := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hzE φ hφ).1
  have hXE : ∀ φ ∈ (LS U T).map z, ∀ τ w, cap τ w φ = ((σ τ).map (fun x => w + (s : ℂ) / 2 + x)).prod • φ := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hzE φ hφ).2
  have hinf := inf_piece mm hmmN hσ hXE
  obtain ⟨S₁, hS₁, hgen⟩ := hfg
  have haut : ∀ φ ∈ (LS U T).map z, IsAutForm φ := fun φ hφ => BlockSlices.LS_aut hT φ (hXle hφ)
  refine BlockTwistCharacters.hyp_tw (-(s : ℂ) / 2) ⟨isStable_map (BlockSlices.LS_stable hU hT) hzc, haut⟩ (finGen_map hzc S₁ hS₁ hgen)
    ⟨_, hinf τ⟩ (fun τ' => ⟨_, hinf τ'⟩) ?_ (BlockTwistCharacters.centIm_left _ hpE fun φ hφ => LS_cent hT φ (hXle hφ))
  refine BlockTwistCharacters.nonPos_tw _ _ haut fun φ hφ r' hr' hrr c' hc' => ?_
  have hb := LS_exp hU hNP hT φ (hXle hφ) r' hr' hrr c' hc'
  have hd := d_pos (E := E)
  have h2 : c'.re / (Module.finrank ℚ E : ℝ) ≤ (r' : ℝ) * (((r + s : ℕ) : ℝ) - r') / 2 := by
    rw [div_le_iff₀ hd]
    linarith
  unfold pE
  have e : (-(s : ℂ) / 2).re = -(s : ℝ) / 2 := by simp
  rw [e]
  push_cast at h2 ⊢
  nlinarith

theorem hyp_right (hU : IsAutSt U) (hNP : NonPos U) (hT : IsSliceMap U c T) (hpE : pE E (r + s) r c = 0)
    (mm : (E →+* ℂ) → Multiset ℂ) (hmmN : ∀ τ, (mm τ).Nodup) {ρ : (E →+* ℂ) → Multiset ℂ} (hρ : ρ ∈ adm mm s)
    {z : Module.End ℂ (Sm E s)} (hzc : ∀ o, Commute z (act o))
    (hzE : ∀ φ ∈ RS U T, z φ ∈ Eig (RS U T) ρ (-(r : ℂ) / 2))
    (hfg : ∃ S₁ : Finset (Sm E s), (↑S₁ : Set (Sm E s)) ⊆ RS U T ∧
      ∀ W : Submodule ℂ (Sm E s), IsStable W → (↑S₁ : Set (Sm E s)) ⊆ W → RS U T ≤ W) (τ : E →+* ℂ) :
    Hyp τ (tw ((RS U T).map z) ((r : ℂ) / 2)) := by
  have hXle : (RS U T).map z ≤ RS U T := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hzE φ hφ).1
  have hXE : ∀ φ ∈ (RS U T).map z, ∀ τ w, cap τ w φ = ((ρ τ).map (fun x => w + -(r : ℂ) / 2 + x)).prod • φ := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hzE φ hφ).2
  have hinf := inf_piece mm hmmN hρ hXE
  obtain ⟨S₁, hS₁, hgen⟩ := hfg
  have haut : ∀ φ ∈ (RS U T).map z, IsAutForm φ := fun φ hφ => BlockSlices.RS_aut hT φ (hXle hφ)
  refine BlockTwistCharacters.hyp_tw ((r : ℂ) / 2) ⟨isStable_map (BlockSlices.RS_stable hU hT) hzc, haut⟩ (finGen_map hzc S₁ hS₁ hgen)
    ⟨_, hinf τ⟩ (fun τ' => ⟨_, hinf τ'⟩) ?_ (BlockTwistCharacters.centIm_right _ hpE fun φ hφ => RS_cent hT φ (hXle hφ))
  refine BlockTwistCharacters.nonPos_tw _ _ haut fun φ hφ r₂ hr₂ hrs c₂ hc₂ => ?_
  have hb := RS_exp hU hNP hT φ (hXle hφ) r₂ hr₂ hrs c₂ hc₂
  have hd := d_pos (E := E)
  have hc := BlockTwistCharacters.re_of_pE (E := E) hpE
  have h2 : c₂.re / (Module.finrank ℚ E : ℝ) ≤
      ((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ)) / 2 - (r : ℝ) * s / 2 := by
    rw [div_le_iff₀ hd]
    have e3 : (((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ)) / 2 - (r : ℝ) * s / 2) *
        (Module.finrank ℚ E : ℝ) = (Module.finrank ℚ E : ℝ) * (((r + r₂ : ℕ) : ℝ) *
        (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ))) / 2 - (r : ℝ) * s * (Module.finrank ℚ E : ℝ) / 2 := by ring
    rw [e3, ← hc]
    exact hb
  unfold pE
  have e : ((r : ℂ) / 2).re = (r : ℝ) / 2 := by simp
  rw [e]
  push_cast at h2 ⊢
  nlinarith

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

end
