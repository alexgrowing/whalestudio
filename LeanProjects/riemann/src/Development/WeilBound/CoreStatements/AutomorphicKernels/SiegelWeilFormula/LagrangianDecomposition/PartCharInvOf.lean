import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SbSlice

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

theorem partCharInv_of (hfin : FinPart) : PartCharInv := by
  intro F _ _ ψ hψ κ' κ'' _ _ l hl hinv Ψ hΨ hzero
  classical
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.CharInvForm.exists_schwartz_one (κ'' → mixedEmbedding.mixedSpace F)
  obtain ⟨U₀, hU₀o, hU₀c, -, -⟩ := GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ κ'' Set.univ Filter.univ_mem
  set θf : (κ'' → Af F) → ℂ := GlobalTheory.CharForm.cosetInd U₀ 0 with hθf
  have hθfSB : θf ∈ SB (κ'' → Af F) := GlobalTheory.CharForm.cosetInd_mem_SB U₀ hU₀o hU₀c 0
  have hθf0 : θf 0 = 1 := by simp [hθf, GlobalTheory.CharForm.cosetInd]
  set θ : (κ'' → AF F) → ℂ := pureA F f₀ θf with hθ
  let P : ((κ' ⊕ κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' ⊕ κ'' → AF F) → ℂ) :=
    { toFun := fun Φ x => Φ (Sum.elim (x ∘ Sum.inl) 0) * θ (x ∘ Sum.inr)
      map_add' := fun _ _ => by funext x; simp [add_mul]
      map_smul' := fun _ _ => by funext x; simp [mul_assoc] }
  have hP : ∀ Φ x, P Φ x = Φ (Sum.elim (x ∘ Sum.inl) 0) * θ (x ∘ Sum.inr) := fun _ _ => rfl
  have e1 : ∀ x : κ' ⊕ κ'' → AF F, (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((Sum.elim (x ∘ Sum.inl) 0 : κ' ⊕ κ'' → AF F) i).1) =
      Sum.elim ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ∘ Sum.inl) 0 := by
    intro x; funext j; rcases j with j | j
    · rfl
    · simp only [Sum.elim_inr, Pi.zero_apply]
      exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have e2 : ∀ x : κ' ⊕ κ'' → AF F, (fun i => ((Sum.elim (x ∘ Sum.inl) 0 : κ' ⊕ κ'' → AF F) i).2) =
      Sum.elim ((fun i => (x i).2) ∘ Sum.inl) 0 := by
    intro x; funext j; rcases j with j | j <;> rfl
  have gen : ∀ (f : SchwartzMap (κ' ⊕ κ'' → mixedEmbedding.mixedSpace F) ℂ) (g : (κ' ⊕ κ'' → Af F) → ℂ),
      g ∈ SB (κ' ⊕ κ'' → Af F) → l (pureA F f g) = l (P (pureA F f g)) := by
    intro f g hg
    obtain ⟨fs, hfs⟩ := exists_slice (κ'' := κ'') f
    obtain ⟨f₁, hf₁⟩ := GlobalTheory.SchwartzBox.exists_schwartz_box fs f₀
    set g₁ : (κ' ⊕ κ'' → Af F) → ℂ := fun z => g (Sum.elim (z ∘ Sum.inl) 0) * θf (z ∘ Sum.inr) with hg₁def
    have hg₁ : g₁ ∈ SB (κ' ⊕ κ'' → Af F) := GlobalTheory.SchwartzBox.sb_box (sb_slice hg) hθfSB
    have hPf : P (pureA F f g) = pureA F f₁ g₁ := by
      funext x
      rw [hP]
      simp only [pureA, hθ, hf₁, hfs, hg₁def]
      rw [e1 x, e2 x]
      simp only [Function.comp_def]
      ring
    rw [hPf]
    obtain ⟨T, hT⟩ := hl g hg
    have hA : T f = T f₁ := by
      have h := arch_part T (fun L f₂ f₃ h23 => by
        obtain ⟨Y, hY⟩ := GlobalTheory.TraceDual.exists_trace_rep F κ'' L
        rw [← hT, ← hT, ← hinv (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0)
          (pureA F f₂ g) (GlobalTheory.CharInvForm.mem_schA f₂ hg)]
        congr 1
        funext x
        simp only [pureA, h23, GlobalTheory.CharInvForm.psi_dot_inf hψ, hY]
        simp only [Function.comp_apply]
        ring) (f - f₁) (fun v hv => by
          have hv' : v = Sum.elim (v ∘ Sum.inl) 0 := by
            funext j; rcases j with j | j
            · rfl
            · exact congrFun hv j
          rw [SchwartzMap.sub_apply, hf₁, hfs, hv, hf₀, mul_one]
          rw [← hv', sub_self])
      rw [map_sub, sub_eq_zero] at h
      exact h
    let a : ((κ' ⊕ κ'' → Af F) → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun h => l (pureA F f₁ h)
        map_add' := fun h h' => by
          rw [← map_add]
          congr 1
          funext x
          simp only [pureA, Pi.add_apply]
          ring
        map_smul' := fun s h => by
          rw [RingHom.id_apply, ← map_smul]
          congr 1
          funext x
          simp only [pureA, Pi.smul_apply, smul_eq_mul]
          ring }
    have hB : a g = a g₁ := by
      have h := hfin F ψ hψ κ' κ'' a (fun y h hh => by
        show l (pureA F f₁ _) = l (pureA F f₁ h)
        rw [← hinv (fun i => pairA F 0 (y i)) (pureA F f₁ h) (GlobalTheory.CharInvForm.mem_schA f₁ hh)]
        congr 1
        funext x
        simp only [pureA, GlobalTheory.CharInvForm.dot_pairA_fin]
        simp only [Function.comp_def]
        ring) (g - g₁) (sub_mem hg hg₁) (fun z' => by
          simp only [Pi.sub_apply, hg₁def, Sum.elim_comp_inl, Sum.elim_comp_inr, hθf0, mul_one, sub_self])
      rw [map_sub, sub_eq_zero] at h
      exact h
    calc l (pureA F f g) = T f := hT f
      _ = T f₁ := hA
      _ = l (pureA F f₁ g) := (hT f₁).symm
      _ = a g := rfl
      _ = a g₁ := hB
      _ = l (pureA F f₁ g₁) := rfl
  have key : ∀ Φ ∈ schA F (κ' ⊕ κ''), l Φ = l (P Φ) := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ hmem =>
      obtain ⟨f, g, hg, rfl⟩ := hmem
      exact gen f g hg
    | zero => simp
    | add _ _ _ _ h h' => rw [map_add, map_add, map_add, h, h']
    | smul c _ _ h => rw [map_smul, map_smul, map_smul, h]
  have h0 : P Ψ = 0 := by
    funext x
    rw [hP, hzero, zero_mul]
    rfl
  rw [key Ψ hΨ, h0, map_zero]

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
