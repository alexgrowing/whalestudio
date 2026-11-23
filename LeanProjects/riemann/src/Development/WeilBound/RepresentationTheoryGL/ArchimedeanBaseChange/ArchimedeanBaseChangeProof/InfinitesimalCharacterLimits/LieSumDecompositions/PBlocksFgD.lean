import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgC

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

def HExp (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) : Prop :=
  ∀ ψ ∈ U, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)), ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s),
    (∀ i, b i ∈ Submodule.span ℂ (BlockDerivatives.lsF r s (T ψ) k g)) ∧ (∀ i, q i ∈ BlockDerivatives.rsF r s (T ψ) k g) ∧
    ∀ m : GA E r × GA E s, (T ψ).1 (lev (Ad E) r s m * BlockDerivatives.yp k g) = ∑ i, (b i).1 m.1 * (q i).1 m.2

theorem lsF_yp (F : Sm E (r + s)) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ∀ ℓ ∈ BlockDerivatives.lsF r s F k g, ∃ m₂, ℓ = sl0 m₂ (rt E (r + s) (BlockDerivatives.yp k g) F) := by
  rintro ℓ ⟨m₂, h⟩
  exact ⟨m₂, Subtype.ext (funext fun m₁ => by rw [h, left_slice_apply, rt_apply])⟩

theorem rsF_yp (F : Sm E (r + s)) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ∀ ℓ ∈ BlockDerivatives.rsF r s F k g, ∃ m₁, ℓ = sl1 m₁ (rt E (r + s) (BlockDerivatives.yp k g) F) := by
  rintro ℓ ⟨m₁, h⟩
  exact ⟨m₁, Subtype.ext (funext fun m₂ => by rw [h, right_slice_apply, rt_apply])⟩

theorem rt_one {a : ℕ} (F : Sm E a) : rt E a (BlockDerivatives.yp 1 1) F = F := by
  rw [yp_one, map_one, Module.End.one_apply]

theorem lsF_one (F : Sm E (r + s)) : ∀ ℓ ∈ BlockDerivatives.lsF r s F 1 1, ∃ m₂, ℓ = sl0 m₂ F := by
  intro ℓ hℓ
  obtain ⟨m₂, h⟩ := lsF_yp F 1 1 ℓ hℓ
  exact ⟨m₂, by rw [h, rt_one]⟩

theorem rsF_one (F : Sm E (r + s)) : ∀ ℓ ∈ BlockDerivatives.rsF r s F 1 1, ∃ m₁, ℓ = sl1 m₁ F := by
  intro ℓ hℓ
  obtain ⟨m₁, h⟩ := rsF_yp F 1 1 ℓ hℓ
  exact ⟨m₁, by rw [h, rt_one]⟩

theorem exp_one {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} (hexp : HExp U T)
    {ψ : Sm E (r + s)} (hψ : ψ ∈ U) :
    ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s),
      (∀ i, b i ∈ Submodule.span ℂ (BlockDerivatives.lsF r s (T ψ) 1 1)) ∧ (∀ i, q i ∈ BlockDerivatives.rsF r s (T ψ) 1 1) ∧
      ∀ m : GA E r × GA E s, (T ψ).1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2 := by
  obtain ⟨n, b, q, hb, hq, he⟩ := hexp ψ hψ 1 1
  refine ⟨n, b, q, hb, hq, fun m => ?_⟩
  rw [← he m, yp_one, mul_one]

theorem rt_yp_eq {a : ℕ} (k : Kinf E a) (g : GL (Fin a) (Af E)) (φ : Sm E a) :
    rt E a (BlockDerivatives.yp k g) φ = act (.cpt k) (act (.fin g) φ) := by
  rw [act_cpt_eq, act_fin_eq, rt_yp_rt, mul_one, one_mul]

theorem rt_yp_mem {a : ℕ} {U : Submodule ℂ (Sm E a)} (hU : IsStable U) (k : Kinf E a) (g : GL (Fin a) (Af E))
    {φ : Sm E a} (hφ : φ ∈ U) : rt E a (BlockDerivatives.yp k g) φ ∈ U := by
  rw [rt_yp_eq]
  exact hU _ _ (hU _ _ hφ)

theorem T_rt_yp {a : ℕ} {U : Submodule ℂ (Sm E a)} (hU : IsStable U) {T : Sm E a →ₗ[ℂ] Sm E a}
    (hT : ∀ o, ∀ φ ∈ U, T (act o φ) = act o (T φ)) (k : Kinf E a) (g : GL (Fin a) (Af E)) {φ : Sm E a}
    (hφ : φ ∈ U) : T (rt E a (BlockDerivatives.yp k g) φ) = rt E a (BlockDerivatives.yp k g) (T φ) := by
  rw [rt_yp_eq, rt_yp_eq, hT _ _ (hU _ _ hφ), hT _ _ hφ]

def Mleft (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) (W : Submodule ℂ (Sm E r)) :
    Submodule ℂ (Sm E (r + s)) where
  carrier := {ψ | ψ ∈ U ∧ ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₂ : GA E s),
    sl0 m₂ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ)) ∈ W}
  add_mem' := fun {a b} ha hb => ⟨U.add_mem ha.1 hb.1, fun k g m₂ => by
    rw [map_add, map_add, map_add]; exact W.add_mem (ha.2 k g m₂) (hb.2 k g m₂)⟩
  zero_mem' := ⟨U.zero_mem, fun k g m₂ => by rw [map_zero, map_zero, map_zero]; exact W.zero_mem⟩
  smul_mem' := fun c a ha => ⟨U.smul_mem c ha.1, fun k g m₂ => by
    rw [map_smul, map_smul, map_smul]; exact W.smul_mem c (ha.2 k g m₂)⟩

def Mright (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) (W : Submodule ℂ (Sm E s)) :
    Submodule ℂ (Sm E (r + s)) where
  carrier := {ψ | ψ ∈ U ∧ ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₁ : GA E r),
    sl1 m₁ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ)) ∈ W}
  add_mem' := fun {a b} ha hb => ⟨U.add_mem ha.1 hb.1, fun k g m₁ => by
    rw [map_add, map_add, map_add]; exact W.add_mem (ha.2 k g m₁) (hb.2 k g m₁)⟩
  zero_mem' := ⟨U.zero_mem, fun k g m₁ => by rw [map_zero, map_zero, map_zero]; exact W.zero_mem⟩
  smul_mem' := fun c a ha => ⟨U.smul_mem c ha.1, fun k g m₁ => by
    rw [map_smul, map_smul, map_smul]; exact W.smul_mem c (ha.2 k g m₁)⟩

theorem Mleft_stable {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ}
    {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} (hT : IsSliceMap U c T) (hexp : HExp U T) (W : Submodule ℂ (Sm E r))
    (hW : IsStable W) : IsStable (Mleft U T W) := by
  rintro o ψ ⟨hψU, hψ⟩
  cases o with
  | fin h =>
    refine ⟨hU.1 _ _ hψU, fun k g m₂ => ?_⟩
    rw [act_fin_eq, rt_yp_rt, mul_one]
    exact hψ k (g * h) m₂
  | cpt κ =>
    refine ⟨hU.1 _ _ hψU, fun k g m₂ => ?_⟩
    rw [act_cpt_eq, rt_yp_rt, mul_one]
    exact hψ (k * κ) g m₂
  | lie X =>
    refine ⟨hU.1 _ _ hψU, fun k g m₂ => ?_⟩
    obtain ⟨X', hX'⟩ := rt_lie_yp k g X
    have hψ'U : rt E (r + s) (BlockDerivatives.yp k g) ψ ∈ U := rt_yp_mem hU.1 k g hψU
    have e1 : rt E (r + s) (BlockDerivatives.yp k g) (act (.lie X) ψ) = lie E (r + s) X' (rt E (r + s) (BlockDerivatives.yp k g) ψ) :=
      LinearMap.congr_fun hX' ψ
    rw [e1]
    have e2 := hT.equiv (.lie X') _ hψ'U
    change T (lie E (r + s) X' _) = lie E (r + s) X' _ at e2
    rw [e2]
    set ψ' := rt E (r + s) (BlockDerivatives.yp k g) ψ with hψ'
    have hP : ∀ m₂, sl0 m₂ (T ψ') ∈ W := fun m₂ => hψ k g m₂
    obtain ⟨n, b, q, hb, -, he⟩ := exp_one hexp hψ'U
    have hsub : BlockDerivatives.lsF r s (T ψ') 1 1 ⊆ W := fun ℓ hℓ => by
      obtain ⟨m, rfl⟩ := lsF_one _ ℓ hℓ
      exact hP m
    have hbW : ∀ i, b i ∈ W := fun i => (Submodule.span_le.2 hsub) (hb i)
    rw [lie_split, map_add]
    refine W.add_mem (key_left W hW (T ψ') (hT.unipInv ψ' hψ'U) hP b q hbW he _ (par_low X') m₂) ?_
    have e3 := hT.equiv (.lie (toL (skw X'))) _ hψ'U
    change T (lie E (r + s) (toL (skw X')) ψ') = lie E (r + s) (toL (skw X')) (T ψ') at e3
    rw [← e3]
    have : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan ψ') := (hU.2 ψ' hψ'U).kfin
    have hmem := lie_mem_orbSpan ψ' (skw X') (skw_skew X')
    have hle : GlobalTheory.CuspRep.LocEx.orbSpan ψ' ≤ W.comap (sl0 m₂ ∘ₗ T) := Submodule.span_le.2 (by
      rintro _ ⟨κ, rfl⟩
      change sl0 m₂ (T (act (.cpt κ) ψ')) ∈ W
      rw [act_cpt_eq, hψ', rt_yp_rt, one_mul]
      exact hψ (κ * k) g m₂)
    exact hle hmem

theorem Mright_stable {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ}
    {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} (hT : IsSliceMap U c T) (hexp : HExp U T) (W : Submodule ℂ (Sm E s))
    (hW : IsStable W) : IsStable (Mright U T W) := by
  rintro o ψ ⟨hψU, hψ⟩
  cases o with
  | fin h =>
    refine ⟨hU.1 _ _ hψU, fun k g m₁ => ?_⟩
    rw [act_fin_eq, rt_yp_rt, mul_one]
    exact hψ k (g * h) m₁
  | cpt κ =>
    refine ⟨hU.1 _ _ hψU, fun k g m₁ => ?_⟩
    rw [act_cpt_eq, rt_yp_rt, mul_one]
    exact hψ (k * κ) g m₁
  | lie X =>
    refine ⟨hU.1 _ _ hψU, fun k g m₁ => ?_⟩
    obtain ⟨X', hX'⟩ := rt_lie_yp k g X
    have hψ'U : rt E (r + s) (BlockDerivatives.yp k g) ψ ∈ U := rt_yp_mem hU.1 k g hψU
    have e1 : rt E (r + s) (BlockDerivatives.yp k g) (act (.lie X) ψ) = lie E (r + s) X' (rt E (r + s) (BlockDerivatives.yp k g) ψ) :=
      LinearMap.congr_fun hX' ψ
    rw [e1]
    have e2 := hT.equiv (.lie X') _ hψ'U
    change T (lie E (r + s) X' _) = lie E (r + s) X' _ at e2
    rw [e2]
    set ψ' := rt E (r + s) (BlockDerivatives.yp k g) ψ with hψ'
    have hP : ∀ m₁, sl1 m₁ (T ψ') ∈ W := fun m₁ => hψ k g m₁
    obtain ⟨n, b, q, -, hq, he⟩ := exp_one hexp hψ'U
    have hqW : ∀ i, q i ∈ W := fun i => by
      obtain ⟨m, hm⟩ := rsF_one _ _ (hq i)
      rw [hm]
      exact hP m
    rw [lie_split, map_add]
    refine W.add_mem (key_right W hW (T ψ') (hT.unipInv ψ' hψ'U) hP b q hqW he _ (par_low X') m₁) ?_
    have e3 := hT.equiv (.lie (toL (skw X'))) _ hψ'U
    change T (lie E (r + s) (toL (skw X')) ψ') = lie E (r + s) (toL (skw X')) (T ψ') at e3
    rw [← e3]
    have : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan ψ') := (hU.2 ψ' hψ'U).kfin
    have hmem := lie_mem_orbSpan ψ' (skw X') (skw_skew X')
    have hle : GlobalTheory.CuspRep.LocEx.orbSpan ψ' ≤ W.comap (sl1 m₁ ∘ₗ T) := Submodule.span_le.2 (by
      rintro _ ⟨κ, rfl⟩
      change sl1 m₁ (T (act (.cpt κ) ψ')) ∈ W
      rw [act_cpt_eq, hψ', rt_yp_rt, one_mul]
      exact hψ (κ * k) g m₁)
    exact hle hmem

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
