import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsFull
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsExtZ
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoStatement
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfSurj
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ContinuousFinId
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj

noncomputable section

namespace PositivityTheory.KCo

section Local

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

def augF (n d : ℕ) (ν α : kˣ →* ℂˣ) : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ) :=
  Submodule.span ℂ {z | ∃ g : GL (Fin n) k, ∃ Φ, Full Φ ∧ z = omB ν α g 1 Φ - Φ}

theorem augF_le {ν α : kˣ →* ℂˣ} : augF n d ν α ≤ aug n d ν α :=
  Submodule.span_mono fun _ ⟨g, Φ, h, e⟩ => ⟨g, Φ, h.1, e⟩

theorem irrF (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) {ν α : kˣ →* ℂˣ} (hnd : n ≤ d) (hν : USm ν)
    (N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ)) (hA : aug n d ν α ≤ N)
    (hN : ∀ h : GL (Fin d) k, ∀ Φ ∈ N, Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) → omB ν α 1 h Φ ∈ N) :
    (∀ Φ, Full Φ → Φ ∈ N) ∨ ∀ Φ ∈ N, Full Φ → Φ ∈ augF n d ν α := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hnd
  have hμ : IsSmoothChar ν⁻¹ := IsSmoothChar.inv hν.2
  obtain ⟨E⟩ := GlobalTheory.T.omega_equiv_induced_fibre k (Fin n) (Fin (n + t)) (Fin n) (Fin t) (stdSum rfl) n (Fintype.card_fin n).symm ν⁻¹ hμ
  have hR : twRel ((omegaOn (Fin n) (Fin (n + t)) ν⁻¹ {n}).comp (MonoidHom.inl _ _)) 1 ≤
      (augF n (n + t) ν α).comap extZ := Submodule.span_le.2 (by
    rintro _ ⟨g, φ, rfl⟩
    refine Submodule.subset_span ⟨g, extZ φ, ⟨extZ_mem φ, fun Y hY => extZ_neg φ (by rwa [rank_transpose])⟩, ?_⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
    congr 1
    refine funext fun Y => (extZ_act _ g 1 φ Y).trans ?_
    have n1 : nabs k 1 = 1 := by simp [nabs]
    simp [omB, omChar, apow, val_absPow, n1])
  rcases irr_equiv E (irr_ind hB n t hμ (fun y => by simp [hν.1 y])) (N.comap extZ) (hR.trans (Submodule.comap_mono (augF_le.trans hA))) (by
    intro h φ hf
    have h1 := hN (invT h) _ hf (extZ_mem φ)
    rw [Submodule.mem_comap]
    have c0 : (α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Units.ne_zero (absPow k ((n : ℂ) / 2) (gdet (invT h))))
    convert N.smul_mem ((omChar (Fin n) (Fin (n + t)) ν⁻¹ (1, h) : ℂ) /
      ((α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2))) h1 using 1
    funext Y
    have e1 : omB ν α 1 (invT h) (extZ φ) Y = (α (gdet (invT h)) : ℂ) * apow (gdet (invT h)) ((n : ℂ) / 2) *
        extZ φ ((1 : GL (Fin n) k).valᵀ * Y * (invT h).val) := by
      simp [omB, apow, nabs]
    rw [extZ_act, Pi.smul_apply, e1, smul_eq_mul, ← mul_assoc, div_mul_cancel₀ _ c0]) with h | h
  · refine Or.inl fun Φ hΦ => ?_
    obtain ⟨φ, rfl⟩ := exists_extZ hΦ
    exact (h ▸ Submodule.mem_top : φ ∈ N.comap extZ)
  · refine Or.inr fun Φ hm hΦ => ?_
    obtain ⟨φ, rfl⟩ := exists_extZ hΦ
    exact hR (h hm)

end Local

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem full_of_soLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (h : IsCMExt F E σ) (hψ : IsStd ψ)
    (hX : X.J.det ≠ 0) (hW : W.J.det ≠ 0) {t : E →ₐ[F] Fv F v} {ι} (hι : M.IsLinBar ψ t 1 1 ι) {φ} (hφ : φ ∈ M.SoLoc ψ t) :
    ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), Y.rank ≠ n → ι φ Y = 0 := by
  obtain ⟨h1, ι', hι', h2⟩ := hφ
  intro Y hY
  obtain ⟨x, hx, h0, rfl⟩ := exists_coB (X := X) (W := W) h t hX hW Y
  exact eigen_kill M h hψ hX hW hι' ((LinearMap.proj (coB σ X W t x)).comp ι) hx h0
    (fun u hu hu1 φ' h' => mult' M hψ hι hu hu1 hx h0 h') h1 (h2 _ hY)

theorem soCoinv_of (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (hD : DictSt) (hK : GlobalTheory.ThK.KFin) :
    PositivityTheory.ThKF.SoCoinv := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT φ hφ hA
  obtain ⟨Rf, hF⟩ := hK F E σ B a a' G X om om' hT
  have ha' : 1 ≤ a' := by have := hT.geo.aBig; omega
  obtain ⟨⟨ι, hι⟩, ν, α, hν, -, h1, hd⟩ := hD F E σ _ _ B G.V' G.W G.M' om' _ _ hT.base ⟨_, _, hT.geo.hV'⟩ ⟨_, _, hT.geo.hW⟩
    hT.geo.hM' hT.weil' hT.chars.heckeα (isHecke_div hT.chars.heckeα hT.chars.heckeβ) B.v₁ B.τ₁
  have hn := nu_statement F E σ B a a' G X om om' hT B.v₁ hT.chars.good
  have hν1 : ν ≠ 1 := fun e => (h1 ha' (by omega) e).elim (hn _) (hn _)
  have hD' := hd ι hι
  have hb := hι.bij
  have := hF.nontriv B.v₁
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdet : ∀ {m : ℕ} (J : Matrix (Fin m) (Fin m) E), (J.map (B.emb w).1).det ≠ 0 → J.det ≠ 0 := fun J hJ h0 =>
    hJ (((RingHom.map_det _ J).symm.trans (congrArg _ h0)).trans (map_zero _))
  have dX : G.V'.J.det ≠ 0 := hdet _ (GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hV'.sig w))
  have dW : G.W.J.det ≠ 0 := hdet _ fun h0 =>
    GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hT.geo.hW.sig w) (by rw [Matrix.det_smul, h0, mul_zero])
  have hs : φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁) := augAt_le hA
  have hf : Full (ι φ) := ⟨hb.1 hs, fun Y hY => by
    have : Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) ≤ LinearMap.ker ((LinearMap.proj Y).comp ι) :=
      Submodule.span_le.2 fun χ hχ => full_of_soLoc G.M' hT.base.cm hT.base.std dX dW hι hχ Y hY
    exact this hφ⟩
  rcases irrF hB (α := α) (by omega) hν ((SB _ ⊓ LinearMap.ker (Rf.p' B.v₁)).map ι)
    ((aug_le_map hb hD').trans (Submodule.map_mono (le_inf augAt_le (hF.inv' _)))) (by
      rintro h₀ _ ⟨ψ, hψ, rfl⟩ -
      obtain ⟨h, hh, hr⟩ := hD'.rightOnto h₀
      obtain ⟨ψ₁, h₁, ha, e⟩ := hr ψ hψ.1
      refine ⟨ψ₁, ⟨h₁, ?_⟩, e⟩
      have h0 : Rf.p' B.v₁ ψ = 0 := hψ.2
      simpa using (hF.equiv _ h hh 0 (zero_mem _) ψ hψ.1 0 (zero_mem _) ψ₁ h₁ (acts_zero _) ha (by simp [h0])).symm) with h | h
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (0 : Rf.Pi B.v₁)
    obtain ⟨ψ, hψ, rfl⟩ : x ∈ (SB _).map (Rf.p' B.v₁) := hF.onto' _ ▸ Submodule.mem_top
    obtain ⟨ψ₀, h₀, hf₀, ha⟩ := exists_full surjectivity_statement hb hD' hν hν1 hψ
    obtain ⟨χ, hχ, e⟩ := h _ hf₀
    have e' : χ = ψ₀ := hb.2.1 hχ.1 h₀ e
    have h2 : Rf.p' B.v₁ (ψ - ψ₀) = 0 := hF.inv' _ ha
    have h3 : Rf.p' B.v₁ ψ₀ = 0 := e' ▸ hχ.2
    exact hx (by rwa [map_sub, h3, sub_zero] at h2)
  · have key : augF a' (a + a') ν α ≤ (SB _ ⊓ PositivityTheory.ThKF.augOn om' B.v₁ (G.M'.SoLoc B.ψ B.τ₁)).map ι := Submodule.span_le.2 (by
      rintro _ ⟨g₀, Φ, hΦ, rfl⟩
      obtain ⟨χ, hχ, rfl⟩ := hb.2.2 hΦ.1
      obtain ⟨g, hg, hr⟩ := hD'.leftOnto g₀
      obtain ⟨χ₁, h₁, ha, e⟩ := hr χ hχ
      exact ⟨χ₁ - χ, ⟨sub_mem h₁ hχ, Submodule.subset_span ⟨g, hg, χ, ⟨hχ, ι, hι, hΦ.2⟩, χ₁, h₁, ha, rfl⟩⟩, by rw [map_sub, e]⟩)
    obtain ⟨χ, hχ, e⟩ := key (h _ ⟨φ, ⟨hs, hF.inv' _ hA⟩, rfl⟩ hf)
    rw [← hb.2.1 hχ.1 hs e]
    exact hχ.2

end PositivityTheory.KCo
