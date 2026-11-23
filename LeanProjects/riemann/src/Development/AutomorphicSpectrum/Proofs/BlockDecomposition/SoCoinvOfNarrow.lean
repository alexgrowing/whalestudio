import Mathlib
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.KCoinvOfDict
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoCoinvariantsOfBernstein
import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.RamifiedMultiplicityOneOfBernstein
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitTop
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.TopOfMap
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.FullOfSoLoc

noncomputable section

namespace GlobalTheory.CompanionTheory.SoCoinvNarrow

open PositivityTheory.KCo

section Narrow

open GlobalTheory.PRep GlobalTheory.SmGL

def NarrowBernstein : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
    (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
    (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible

end Narrow

section Induced

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irr_gen (NB : NarrowBernstein) (n t : ℕ) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ) (hμ1 : μ ≠ 1)
    (hu : ∀ x, ‖(μ x : ℂ)‖ = 1) {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Γ × (GL (Fin n) k × GL (Fin t) k)) W) (hτ : IsSmooth (τ.comp (MonoidHom.inr Γ _)))
    (l : W →ₗ[ℂ] ℂ) (hs : Function.Surjective l)
    (hτl : ∀ g p₁ p₂ φ, l (τ (g, p₁, p₂) φ) = (μ (GeneralLinearGroup.det p₂) : ℂ) * l φ)
    (hk : ∀ x, l x = 0 → x ∈ twRel (τ.comp (MonoidHom.inl Γ _)) 1)
    (N : Submodule ℂ (IndSp (two (stdSum (rfl : n + t = n + t)))
      (MonoidHom.comp (τ.comp (MonoidHom.inr _ _)) (leviTwo k (Fin n) (Fin t)).symm.toMonoidHom)))
    (hR : twRel ((indSnd (stdSum rfl) τ).comp (MonoidHom.inl _ _)) 1 ≤ N)
    (hN : ∀ h, ∀ f ∈ N, indSnd (stdSum rfl) τ (1, h) f ∈ N) :
    N = ⊤ ∨ N ≤ twRel ((indSnd (stdSum rfl) τ).comp (MonoidHom.inl _ _)) 1 := by
  let e := stdSum (rfl : n + t = n + t)
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k _ (Fin (n + t)) _ (two e)
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let ρ : Representation ℂ (Levi k (Two (Fin n) (Fin t))) _ :=
    MonoidHom.comp (τ.comp (MonoidHom.inr Γ _)) (leviTwo k (Fin n) (Fin t)).symm.toMonoidHom
  let π₁ := detRep (Fin n) (1 : kˣ →* ℂˣ)
  let π₂ := detRep (Fin t) μ
  let ρD : Representation ℂ (Levi k (Two (Fin n) (Fin t))) (ℂ ⊗[ℂ] ℂ) :=
    (extTensor π₁ π₂).comp (leviTwo k (Fin n) (Fin t)).symm.toMonoidHom
  let q : ρ.IntertwiningMap ρD :=
    { toLinearMap := (TensorProduct.lid ℂ ℂ).symm.toLinearMap ∘ₗ l
      isIntertwining' := fun m => LinearMap.ext fun φ => by
        change (TensorProduct.lid ℂ ℂ).symm (l (τ (1, m false, m true) φ)) =
          extTensor π₁ π₂ (m false, m true) ((TensorProduct.lid ℂ ℂ).symm (l φ))
        rw [hτl]
        simp [π₁, π₂, detRep] }
  have hq : Function.Surjective q := (TensorProduct.lid ℂ ℂ).symm.surjective.comp hs
  have hρ : IsSmooth ρ := isSmooth_comp hτ _ ((continuous_apply false).prodMk (continuous_apply true))
  have hI : (parInd (two e) ρD).IsIrreducible :=
    NB k n t 1 μ (by unfold IsSmoothChar; simp) hμ (fun _ => by simp) hu (Or.inr hμ1.symm)
  let σ := (twist ρ (deltaHalf k (Two (Fin n) (Fin t)))).comp (leviProj k (two e))
  have hσ : IsSmooth σ := isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ hcont
  let α : Representation.IntertwiningMap σ ((twist ρD (deltaHalf k (Two (Fin n) (Fin t)))).comp (leviProj k (two e))) :=
    compMap (twistMap q _) _
  let T : Γ → Representation.IntertwiningMap σ σ := fun γ =>
    compMap (twistMap (actFst τ γ) (deltaHalf k (Two (Fin n) (Fin t)))) (leviProj k (two e))
  have hker0 : ∀ x, α x = 0 → x ∈ Submodule.span ℂ {y | ∃ γ z, y = T γ z - z} := by
    intro x hx
    have h0 : l x = 0 := (TensorProduct.lid ℂ ℂ).symm.map_eq_zero_iff.1 hx
    refine (Submodule.span_le (p := Submodule.span ℂ {y | ∃ γ z, y = T γ z - z})).2 ?_ (hk x h0)
    rintro _ ⟨γ, v, rfl⟩
    refine Submodule.subset_span ⟨γ, v, ?_⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    rfl
  obtain ⟨-, hker⟩ := GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (GL (Fin (n + t)) k) (parab k (two e)) (KO k _) hP
    GlobalTheory.SplitFlip.isCompact_KO hPK (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k _) _ _ σ _ hσ α _ T (fun y => hq y) hker0
  let Φ : (parInd (two e) ρ).IntertwiningMap (parInd (two e) ρD) := parIndMap (two e) q
  have hK : ∀ f, Φ f = 0 → f ∈ twRel ((indSnd e τ).comp (MonoidHom.inl _ _)) 1 := fun f hf => by
    refine (Submodule.span_le (p := twRel ((indSnd e τ).comp (MonoidHom.inl _ _)) 1)).2 ?_ (hker f hf)
    rintro _ ⟨γ, z, rfl⟩
    refine Submodule.subset_span ⟨γ, z, ?_⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    congr 1
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show τ (γ, 1) (z.1.1 x) = τ (γ, 1) (z.1.1 (x * 1))
    rw [mul_one]
  let S : Subrepresentation (parInd (two e) ρD) := ⟨N.map Φ.toLinearMap, by
    rintro h _ ⟨f, hf, rfl⟩
    refine ⟨_, hN h f hf, ?_⟩
    rw [indSnd_inr]
    exact Φ.isIntertwining _ _ h f⟩
  rcases hI.eq_bot_or_eq_top S with h | h
  · refine Or.inr fun f hf => hK f ?_
    have : Φ.toLinearMap f ∈ S.toSubmodule := ⟨f, hf, rfl⟩
    rw [h] at this
    exact this
  · exact Or.inl (top_of_map Φ.toLinearMap hK hR (congrArg Subrepresentation.toSubmodule h))

theorem irr_ind (NB : NarrowBernstein) (n t : ℕ) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ) (hμ1 : μ ≠ 1)
    (hu : ∀ x, ‖(μ x : ℂ)‖ = 1) (N : Submodule ℂ (IndSp (two (stdSum (rfl : n + t = n + t)))
      (MonoidHom.comp ((fibRep (Fin n) (Fin n) (Fin t) μ n).comp (MonoidHom.inr _ _)) (leviTwo k (Fin n) (Fin t)).symm.toMonoidHom)))
    (hR : twRel ((indSnd (stdSum rfl) (fibRep (Fin n) (Fin n) (Fin t) μ n)).comp (MonoidHom.inl _ _)) 1 ≤ N)
    (hN : ∀ h, ∀ f ∈ N, indSnd (stdSum rfl) (fibRep (Fin n) (Fin n) (Fin t) μ n) (1, h) f ∈ N) :
    N = ⊤ ∨ N ≤ twRel ((indSnd (stdSum rfl) (fibRep (Fin n) (Fin n) (Fin t) μ n)).comp (MonoidHom.inl _ _)) 1 := by
  let τ := fibRep (Fin n) (Fin n) (Fin t) μ n
  let ξ : GL (Fin n) k →* ℂˣ := detChar (Fin n) (μ⁻¹ * absPow k (((Fintype.card (Fin n) : ℂ) + Fintype.card (Fin t)) / 2))
  have hξ : IsSmoothChar ξ := (hμ.inv.mul (isSmoothChar_of_isUnram (isUnram_absPow k _))).detChar
  obtain ⟨l, hs, hl, hk⟩ := exists_fun (k := k) (κ := n) (Fintype.card_fin n).symm hξ
  have hτ : IsSmooth (τ.comp (MonoidHom.inr _ _)) := GlobalTheory.T.fibre_representation_smooth k _ _ _ μ hμ n
  have hτl : ∀ g p₁ p₂ φ, l (τ (g, p₁, p₂) φ) = (μ (GeneralLinearGroup.det p₂) : ℂ) * l φ := by
    intro g p₁ p₂ φ
    change l ((fibChar (Fin n) (Fin n) (Fin t) μ (g, p₁, p₂) : ℂ) • fibBase (Fin n) (Fin n) n (g, p₁) φ) = _
    rw [map_smul, hl, smul_eq_mul, ← mul_assoc]
    congr 1
    have a1 : ∀ (x : kˣ) (s s' s'' : ℂ), s + s' + s'' = 0 → absPow k s x * absPow k s' x * absPow k s'' x = 1 := fun x s s' s'' h => by
      rw [← MonoidHom.mul_apply, ← absPow_add, ← MonoidHom.mul_apply, ← absPow_add, h]
      exact Units.ext (by simp [val_absPow])
    have b1 := congrArg Units.val (a1 (GeneralLinearGroup.det p₁) (-(n : ℂ) / 2) (-(t : ℂ) / 2) (((n : ℂ) + t) / 2) (by ring))
    have b2 := congrArg Units.val (a1 (GeneralLinearGroup.det p₂) (-(n : ℂ) / 2) ((n : ℂ) / 2) 0 (by ring))
    simp only [fibChar, ξ, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, detChar_apply,
      Units.val_mul, MonoidHom.inv_apply, Fintype.card_fin, Units.val_inv_eq_inv_val, Units.val_one, val_absPow, Complex.cpow_zero,
      mul_one] at b1 b2 ⊢
    have n1 := (μ (GeneralLinearGroup.det g)).ne_zero
    have n2 := (μ (GeneralLinearGroup.det p₁)).ne_zero
    have n3 := (absPow k (((n : ℂ) + t) / 2) (GeneralLinearGroup.det g)).ne_zero
    rw [val_absPow] at n3
    simp only [neg_div] at b1 b2
    field_simp
    linear_combination (exp := 1) ((nabs k (GeneralLinearGroup.det p₂) : ℂ) ^ (-((n : ℂ) / 2)) *
      (nabs k (GeneralLinearGroup.det p₂) : ℂ) ^ ((n : ℂ) / 2)) * b1 + b2
  refine irr_gen NB n t hμ hμ1 hu τ hτ l hs hτl (fun x h0 => ?_) N hR hN
  refine (Submodule.span_le (p := twRel (τ.comp (MonoidHom.inl _ _)) 1)).2 ?_ (hk x h0)
  rintro _ ⟨γ, v, rfl⟩
  have e1 : τ (γ, 1) v = (ξ γ : ℂ) • rightRep (Fin n) (Fin n) n γ v := by
    change (fibChar (Fin n) (Fin n) (Fin t) μ (γ, 1) : ℂ) • fibBase (Fin n) (Fin n) n (γ, 1) v = _
    congr 1
    simp [fibChar, ξ]
  have h : rightRep (Fin n) (Fin n) n γ v - ((ξ⁻¹ γ : ℂˣ) : ℂ) • v =
      ((ξ⁻¹ γ : ℂˣ) : ℂ) • (τ (γ, 1) v - (((1 : GL (Fin n) k →* ℂˣ) γ : ℂˣ) : ℂ) • v) := by
    rw [e1, MonoidHom.one_apply, Units.val_one, one_smul, smul_sub, smul_smul, MonoidHom.inv_apply, Units.inv_mul, one_smul]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, v, rfl⟩)

end Induced

section Local

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

theorem irrF (NB : NarrowBernstein) {ν α : kˣ →* ℂˣ} (hnd : n ≤ d) (hν : USm ν) (hν1 : ν ≠ 1)
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
  rcases irr_equiv E (irr_ind NB n t hμ (inv_ne_one.2 hν1) (fun y => by simp [hν.1 y])) (N.comap extZ) (hR.trans (Submodule.comap_mono (augF_le.trans hA))) (by
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

theorem soCoinv_of (NB : NarrowBernstein) (hD : DictSt) (hK : GlobalTheory.ThK.KFin) :
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
  rcases irrF NB (α := α) (by omega) hν hν1 ((SB _ ⊓ LinearMap.ker (Rf.p' B.v₁)).map ι)
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

open GlobalTheory.PRep GlobalTheory.SmGL in

theorem soCoinv_of_narrow :
    (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
      (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
      (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible) →
    GlobalTheory.ThK.KFin → PositivityTheory.ThKF.SoCoinv :=
  fun NB hK => soCoinv_of NB dictionary_statement hK

end GlobalTheory.CompanionTheory.SoCoinvNarrow
