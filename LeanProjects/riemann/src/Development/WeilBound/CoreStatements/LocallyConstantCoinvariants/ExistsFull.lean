import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.RightOnto

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {om : Rep σ X W} {v : Pl F}
  {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {ν α : (Fv F v)ˣ →* ℂˣ}

theorem augAt_le : augAt om v ≤ SB _ := Submodule.span_le.2 (by
  rintro _ ⟨g, -, φ, h, φ₁, h₁, -, rfl⟩
  exact sub_mem h₁ h)

theorem aug_le_map (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hD : IsDict om v ι ν α) : aug n d ν α ≤ (augAt om v).map ι := Submodule.span_le.2 (by
  rintro _ ⟨g₀, Φ, hΦ, rfl⟩
  obtain ⟨φ, hφ, rfl⟩ := hb.2.2 hΦ
  obtain ⟨g, hg, h⟩ := hD.leftOnto g₀
  obtain ⟨φ₁, h₁, ha, e⟩ := h φ hφ
  exact ⟨φ₁ - φ, Submodule.subset_span ⟨g, hg, φ, hφ, φ₁, h₁, ha, rfl⟩, by rw [map_sub, e]⟩)

theorem mem_augAt (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hD : IsDict om v ι ν α) {φ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) (h : ι φ ∈ aug n d ν α) : φ ∈ augAt om v := by
  obtain ⟨ψ, hψ, e⟩ := aug_le_map hb hD h
  rwa [← hb.2.1 (augAt_le hψ) hφ e]

theorem exists_full (hS : SurjSt) (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hD : IsDict om v ι ν α) (hν : USm ν) (h1 : ν ≠ 1) {φ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) :
    ∃ φ₀ ∈ SB (Fin n × Fin d → Fv F v), Full (ι φ₀) ∧ φ - φ₀ ∈ augAt om v := by
  obtain ⟨Φ₀, h0, h⟩ := hS _ n d ν α hν h1 _ (hb.1 hφ)
  obtain ⟨φ₀, hφ₀, rfl⟩ := hb.2.2 h0.1
  exact ⟨φ₀, hφ₀, h0, mem_augAt hb hD (sub_mem hφ hφ₀) (by rwa [map_sub])⟩

theorem ker_eq (hS : SurjSt) (hI : IrrSt) (hnd : n ≤ d)
    (hb : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (hD : IsDict om v ι ν α) (hν : USm ν) (hα : USm α) (h1 : ν ≠ 1) {P : Type} [AddCommGroup P] [Module ℂ P] [Nontrivial P]
    (p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P) (onto : (SB _).map p = ⊤) (inv : augAt om v ≤ LinearMap.ker p)
    (st : ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → p φ = 0 → p φ₁ = 0) :
    ∀ φ ∈ SB _, p φ = 0 ↔ φ ∈ augAt om v := by
  intro φ hφ
  refine ⟨fun h0 => ?_, fun h => inv h⟩
  rcases hI _ n d ν α hnd hν hα ((SB _ ⊓ LinearMap.ker p).map ι)
    ((aug_le_map hb hD).trans (Submodule.map_mono (le_inf augAt_le inv))) (by
      rintro h₀ _ ⟨ψ, hψ, rfl⟩ -
      obtain ⟨h, hh, hr⟩ := hD.rightOnto h₀
      obtain ⟨ψ₁, h₁, ha, e⟩ := hr ψ hψ.1
      exact ⟨ψ₁, ⟨h₁, st h hh ψ hψ.1 ψ₁ h₁ ha hψ.2⟩, e⟩) with h | h
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (0 : P)
    obtain ⟨ψ, hψ, rfl⟩ : x ∈ (SB _).map p := onto ▸ Submodule.mem_top
    obtain ⟨ψ₀, h₀, hf, ha⟩ := exists_full hS hb hD hν h1 hψ
    obtain ⟨χ, hχ, e⟩ := h _ hf
    have e' : χ = ψ₀ := hb.2.1 hχ.1 h₀ e
    have h2 : p (ψ - ψ₀) = 0 := inv ha
    have h3 : p ψ₀ = 0 := e' ▸ hχ.2
    exact hx (by rwa [map_sub, h3, sub_zero] at h2)
  · obtain ⟨φ₀, h₀, hf, ha⟩ := exists_full hS hb hD hν h1 hφ
    have h2 : p (φ - φ₀) = 0 := inv ha
    have h3 : p φ₀ = 0 := by rwa [map_sub, h0, zero_sub, neg_eq_zero] at h2
    have := add_mem ha (mem_augAt hb hD h₀ (h _ ⟨φ₀, ⟨h₀, h3⟩, rfl⟩ hf))
    rwa [sub_add_cancel] at this

theorem acts_zero (γ : UA σ X.J × UA σ W.J) : Acts (evFin F v) (om γ) (0 : (Fin n × Fin d → Fv F v) → ℂ) 0 := fun r _ => by
  have : tens (evFin F v) (0 : (Fin n × Fin d → Fv F v) → ℂ) r = 0 := funext fun x => by simp [tens]
  rw [this, map_zero]

theorem chrW_div_ne {χ χ' : Chr F E} {t : E →ₐ[F] Fv F v} (h : chrW (χ / χ') t ≠ 1) : chrW (χ' / χ) t ≠ 1 := fun e =>
  h (MonoidHom.ext fun x => by
    have := DFunLike.congr_fun e x
    simp only [chrW, locChar, MonoidHom.comp_apply, MonoidHom.div_apply, MonoidHom.one_apply] at this ⊢
    rw [map_div, div_eq_one] at this ⊢
    exact this.symm)

theorem isHecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2, h'.2, div_one]⟩

def GoodSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl F, SplitsFully E v → Nonempty (E →ₐ[F] Fv F v)

theorem kCoinv_of (hS : SurjSt) (hI : IrrSt) (hD : DictSt) (hN : NuSt) (hSo : SoSt) (hG : GoodSplit) : GlobalTheory.ThK.KCoinv := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hM
  have hT := hM.triple
  have hF := hM.fin
  refine ⟨fun v hv => ?_, hSo F E σ B a a' G X om om' hT⟩
  have ha' : 1 ≤ a' := by have := hT.geo.aBig; omega
  have ha : 1 ≤ a := by have := hT.geo.lt; omega
  have D1 := fun t => hD F E σ _ _ B G.V G.W G.M om _ _ hT.base ⟨_, _, hT.geo.hV⟩ ⟨_, _, hT.geo.hW⟩ hT.geo.hM hT.weil
    hT.chars.heckeβ (isHecke_div hT.chars.heckeβ hT.chars.heckeα) v t
  have D2 := fun t => hD F E σ _ _ B G.V' G.W G.M' om' _ _ hT.base ⟨_, _, hT.geo.hV'⟩ ⟨_, _, hT.geo.hW⟩ hT.geo.hM' hT.weil'
    hT.chars.heckeα (isHecke_div hT.chars.heckeα hT.chars.heckeβ) v t
  have hn := hN F E σ B a a' G X om om' hT v hv
  have := hF.nontriv v
  obtain ⟨t₀⟩ : Nonempty (E →ₐ[F] Fv F v) := hG F E σ B hT.base v hv.2
  have k2 : ∀ φ ∈ SB _, Rf.p' v φ = 0 ↔ φ ∈ augAt om' v := by
    obtain ⟨⟨ι, hι⟩, ν, α, hν, hα, h1, h⟩ := D2 t₀
    exact ker_eq hS hI (by omega) hι.bij (h ι hι) hν hα (fun e => (h1 ha' (by omega) e).elim (hn _) (hn _)) _ (hF.onto' v) (hF.inv' v)
      fun g hg φ hφ φ₁ h₁ hA h0 => by
        simpa using (hF.equiv v g hg 0 (zero_mem _) φ hφ 0 (zero_mem _) φ₁ h₁ (acts_zero _) hA (by simp [h0])).symm
  refine ⟨?_, k2, fun t ξ => ?_, fun l hl => ?_⟩
  · obtain ⟨⟨ι, hι⟩, ν, α, hν, hα, h1, h⟩ := D1 t₀
    exact ker_eq hS hI (by omega) hι.bij (h ι hι) hν hα
      (fun e => (h1 ha (by omega) e).elim (chrW_div_ne (hn _)) (chrW_div_ne (hn _))) _ (hF.onto v) (hF.inv v)
      fun g hg φ hφ φ₁ h₁ hA h0 => by
        simpa using hF.equiv v g hg φ hφ 0 (zero_mem _) φ₁ h₁ 0 (zero_mem _) hA (acts_zero _) (by simp [h0])
  · obtain ⟨⟨ι, hι⟩, ν, α, hν, hα, h1, h⟩ := D2 t
    obtain ⟨ψ, hψ, rfl⟩ : ξ ∈ (SB _).map (Rf.p' v) := hF.onto' v ▸ Submodule.mem_top
    obtain ⟨ψ₀, h₀, hf, hA⟩ := exists_full hS hι.bij (h ι hι) hν (fun e => (h1 ha' (by omega) e).elim (hn _) (hn _)) hψ
    have h2 : Rf.p' v (ψ - ψ₀) = 0 := hF.inv' v hA
    exact ⟨ψ₀, ⟨h₀, ι, hι, hf.2⟩, by rw [map_sub, sub_eq_zero] at h2; exact h2.symm⟩
  · let q := (Rf.p' v).domRestrict (SB _)
    have hq : LinearMap.range q = ⊤ := by rw [LinearMap.range_domRestrict, hF.onto' v]
    obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective hq
    refine ⟨(l.domRestrict (SB _)).comp s, fun φ hφ => ?_⟩
    have e : Rf.p' v (s (Rf.p' v φ) : _) = Rf.p' v φ := LinearMap.congr_fun hs _
    have h0 : l (φ - (s (Rf.p' v φ) : _)) = 0 :=
      hl ((k2 _ (sub_mem hφ (s _).2)).1 (by rw [map_sub, e, sub_self]))
    rw [map_sub, sub_eq_zero] at h0
    exact h0

end PositivityTheory.KCo
