import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PScKey
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PScFin
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PScLin

noncomputable section
open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.Tail.PSc

section Sm

variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem smVec_add {x y : V} (hx : SmVec ρ x) (hy : SmVec ρ y) : SmVec ρ (x + y) := by
  obtain ⟨U, hU, hxU⟩ := hx
  obtain ⟨U', hU', hyU⟩ := hy
  refine ⟨U ⊓ U', hU.inter hU', mem_fixed_iff'.2 fun g hg => ?_⟩
  rw [map_add, mem_fixed_iff'.1 hxU g (Subgroup.mem_inf.1 hg).1, mem_fixed_iff'.1 hyU g (Subgroup.mem_inf.1 hg).2]

theorem smVec_smul (c : ℂ) {x : V} (hx : SmVec ρ x) : SmVec ρ (c • x) := by
  obtain ⟨U, hU, hxU⟩ := hx
  exact ⟨U, hU, (fixed ρ U).smul_mem c hxU⟩

theorem smVec_zero : SmVec ρ (0 : V) := ⟨⊤, by simp, (fixed ρ ⊤).zero_mem⟩

theorem smVec_sum {ι : Type} (s : Finset ι) (f : ι → V) (hf : ∀ i ∈ s, SmVec ρ (f i)) :
    SmVec ρ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (smVec_zero (ρ := ρ))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact smVec_add (hf i (Finset.mem_insert_self _ _)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end Sm

theorem eq_of_dual {W : Type} [AddCommGroup W] [Module ℂ W] {v v' : W} (h : ∀ lw : W →ₗ[ℂ] ℂ, lw v = lw v') :
    v = v' := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (v - v')).1 fun φ => ?_
  rw [map_sub, h φ, sub_self]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def chiMu (μ : HChar E) (w : Pl E) (a b : ℕ) : GLw a w × GLw b w →* ℂˣ :=
  (((μ ^ b).loc w).comp GeneralLinearGroup.det).comp (MonoidHom.fst _ _) *
    (((μ ^ a).loc w).comp GeneralLinearGroup.det).comp (MonoidHom.snd _ _)

theorem chiMu_apply (μ : HChar E) (w : Pl E) (a b : ℕ) (g : GLw a w × GLw b w) :
    ((chiMu μ w a b g : ℂˣ) : ℂ) = ((((μ ^ b).loc w).comp GeneralLinearGroup.det) g.1 : ℂ) *
      ((((μ ^ a).loc w).comp GeneralLinearGroup.det) g.2 : ℂ) := by
  simp [chiMu]

theorem isOpen_chiMu (μ : HChar E) (w : Pl E) (a b : ℕ) :
    IsOpen ((chiMu μ w a b).ker : Set (GLw a w × GLw b w)) := by
  have h1 : GlobalTheory.SmGL.IsSmoothChar
      ((((μ ^ b).loc w).comp GeneralLinearGroup.det).comp (MonoidHom.fst (GLw a w) (GLw b w))) :=
    ((ParLaws.isSmoothChar_loc (μ ^ b) w).comp _ GlobalTheory.SmGL.continuous_glDet).comp _ continuous_fst
  have h2 : GlobalTheory.SmGL.IsSmoothChar
      ((((μ ^ a).loc w).comp GeneralLinearGroup.det).comp (MonoidHom.snd (GLw a w) (GLw b w))) :=
    ((ParLaws.isSmoothChar_loc (μ ^ a) w).comp _ GlobalTheory.SmGL.continuous_glDet).comp _ continuous_snd
  exact GlobalTheory.SmGL.IsSmoothChar.mul h1 h2

theorem phiMu_eq {n a b : ℕ} (h : a + b = n) (w : Pl E) (μ : HChar E) (e : GLw n w → ℂ) (x y : GLw n w)
    (g : GLw a w × GLw b w) : phiMu h w (μ.loc w) e x y g =
      ((μ.loc w ((-1) ^ (a * b)) : ℂˣ) : ℂ) * ((chiMu μ w a b g : ℂˣ) : ℂ) * phi3 h w e x y g := by
  rw [phiMu, mu_fac, chiMu_apply, mul_assoc]

theorem tw_eq {a b : ℕ} {w : Pl E} {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (ρ₁ : Representation ℂ (GLw a w) V₁) (ρ₂ : Representation ℂ (GLw b w) V₂) (μ : HChar E) (g : GLw a w × GLw b w)
    (v : V₁ ⊗[ℂ] V₂) :
    GlobalTheory.SmGL.extTensor (twRep ρ₁ (((μ ^ b).loc w).comp GeneralLinearGroup.det))
      (twRep ρ₂ (((μ ^ a).loc w).comp GeneralLinearGroup.det)) g v =
      ((chiMu μ w a b g : ℂˣ) : ℂ) • GlobalTheory.SmGL.extTensor ρ₁ ρ₂ g v := by
  rw [extTensor_twRep, chiMu_apply]

theorem transport {n : ℕ} {w : Pl E} {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (GLw n w) V₁) (π₂ : Representation ℂ (GLw n w) V₂) (Ψ : π₁.Equiv π₂)
    (K : Subgroup (GLw n w)) (e : GLw n w → ℂ) (he : IsHk K e) (u : V₁) (hu : u ∈ fixed π₁ K) (k : ℕ)
    (hne : (hk π₁ K e)^[k] u ≠ 0) : Ψ u ∈ fixed π₂ K ∧ (hk π₂ K e)^[k] (Ψ u) ≠ 0 := by
  have hΨ : ∀ g v, Ψ (π₁ g v) = π₂ g (Ψ v) := fun g v => by
    simpa using LinearMap.congr_fun (Ψ.isIntertwining' g) v
  have hT : ∀ v, Ψ (hk π₁ K e v) = hk π₂ K e (Ψ v) := by
    intro v
    unfold hk
    rw [map_finsum Ψ (hk_supp π₁ K e he v)]
    refine finsum_congr fun q => ?_
    rw [map_smul, hΨ q.out v]
  have hTi : ∀ i v, Ψ ((hk π₁ K e)^[i] v) = (hk π₂ K e)^[i] (Ψ v) := by
    intro i
    induction i with
    | zero => intro v; rfl
    | succ i ih =>
      intro v
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hT, ih]
  refine ⟨mem_fixed_iff'.2 fun g hg => ?_, ?_⟩
  · rw [← hΨ, mem_fixed_iff'.1 hu g hg]
  · rw [← hTi]
    intro h0
    exact hne (Ψ.injective (h0.trans (map_zero Ψ).symm))

theorem core {n a b : ℕ} (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (S : Submodule ℂ (H E a b → ℂ)) (hinv : ∀ g, ∀ x ∈ S, pairRt a b w g x ∈ S)
    {Y : Type} [AddCommGroup Y] [Module ℂ Y] (τ ρ : Representation ℂ (GLw a w × GLw b w) Y)
    {J : Type} (Λ : J → (H E a b → ℂ) →ₗ[ℂ] Y)
    (heq : ∀ j g, ∀ x ∈ S, SmVec (pairRt a b w) x → Λ j (pairRt a b w g x) = τ g (Λ j x))
    (hsep : ∀ x ∈ S, SmVec (pairRt a b w) x → (∀ j, Λ j x = 0) → x = 0)
    (χμ : GLw a w × GLw b w →* ℂˣ) (hχμo : IsOpen (χμ.ker : Set (GLw a w × GLw b w)))
    (hρτ : ∀ g v, ρ g v = ((χμ g : ℂˣ) : ℂ) • τ g v) (c₀ : ℂ)
    (e : GLw n w → ℂ)
    (hphiMu : ∀ x y g, phiMu h w μ e x y g = c₀ * ((χμ g : ℂˣ) : ℂ) * phi3 h w e x y g)
    (K' : Subgroup (GLw n w)) (hK'o : IsOpen (K' : Set (GLw n w))) (hK'le : K' ≤ GlobalTheory.LFun.KGL w n)
    (hnorm : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K')
    (X : Finset (GLw n w)) (hXK : ∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w n) (hX : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ X, x⁻¹ * k ∈ K')
    (hHk : IsHk K' e) (L : Subgroup (GLw a w × GLw b w)) (hLo : IsOpen (L : Set (GLw a w × GLw b w)))
    (G : X → H E a b → ℂ) (hG : ∀ x, G x ∈ S ∧ G x ∈ fixed (pairRt a b w) L) (k : ℕ)
    (hne : (matS h w μ e X)^[k + 1] G ≠ 0) {V₂ : Type} [AddCommGroup V₂] [Module ℂ V₂]
    (π₂ : Representation ℂ (GLw n w) V₂) (Ψ : (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ).Equiv π₂) :
    ∃ u ∈ fixed π₂ K', (hk π₂ K' e)^[k] u ≠ 0 := by

  let Lv : Subgroup (GLw a w × GLw b w) := K'.comap (CtLevel.dgM h w)
  have hLvo : IsOpen (Lv : Set (GLw a w × GLw b w)) := hK'o.preimage (GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.continuous_dgM h w)
  have hLv : ∀ k ∈ Lv, k ∈ leviOf h w K' := fun k hk => by
    show blk h w k 0 ∈ K'
    rw [GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.blk_zero_eq]
    exact hk
  have h1Lv : (1 : GLw a w × GLw b w) ∈ leviOf h w K' := by
    show blk h w 1 0 ∈ K'
    rw [GlobalTheory.LeviFubini.blk_one_zero]
    exact K'.one_mem
  have hR : ∀ x ∈ X, ∀ y ∈ X, ∀ g, ∀ k ∈ Lv ⊓ χμ.ker, phiMu h w μ e x y (g * k) = phiMu h w μ e x y g := by
    intro x hx y hy g k hk
    have e1 : phi3 h w e x y (g * k) = phi3 h w e x y g := by
      have := GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_bi_invariant h w K' hK'le hnorm e hHk.2.2.2 x y (hXK x hx) (hXK y hy) 1 k h1Lv
        (hLv k (Subgroup.mem_inf.1 hk).1) g
      simpa using this
    have e2 : ((χμ (g * k) : ℂˣ) : ℂ) = ((χμ g : ℂˣ) : ℂ) := by
      rw [map_mul, MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hk).2, mul_one]
    rw [hphiMu, hphiMu, e1, e2]
  have hcs : ∀ x y, HasCompactSupport (phiMu h w μ e x y) := by
    intro x y
    have e3 : phiMu h w μ e x y = fun g => (c₀ * ((χμ g : ℂˣ) : ℂ)) * phi3 h w e x y g := funext (hphiMu x y)
    rw [e3]
    exact (GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_compact_support h w e hHk.2.2.1 x y).mul_left

  have hGdAct : ∀ x ∈ X, ∀ y ∈ X, ∀ F, F ∈ S → SmVec (pairRt a b w) F →
      actP w (phiMu h w μ e x y) F ∈ S ∧ SmVec (pairRt a b w) (actP w (phiMu h w μ e x y) F) := by
    intro x hx y hy F hFS hFs
    obtain ⟨U₁, hU₁o, hFU₁⟩ := hFs
    have hFU : F ∈ fixed (pairRt a b w) (U₁ ⊓ (Lv ⊓ χμ.ker)) :=
      mem_fixed_iff'.2 fun g hg => mem_fixed_iff'.1 hFU₁ g (Subgroup.mem_inf.1 hg).1
    obtain ⟨S', s, -, -, -, -, hEq⟩ := actP_eq_sum w (U₁ ⊓ (Lv ⊓ χμ.ker)) (hU₁o.inter (hLvo.inter hχμo)) F hFU
      (phiMu h w μ e x y) (hcs x y) (fun g k hk => hR x hx y hy g k (Subgroup.mem_inf.1 hk).2)
    rw [hEq]
    exact ⟨Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (hinv _ F hFS)),
      smVec_smul _ (smVec_sum _ _ fun q _ => smVec_smul _ (GlobalTheory.CompanionTheory.NodeSep.smVec_translate _ ⟨U₁, hU₁o, hFU₁⟩ _))⟩
  have hGd : ∀ i (x : X), (matS h w μ e X)^[i] G x ∈ S ∧ SmVec (pairRt a b w) ((matS h w μ e X)^[i] G x) := by
    intro i
    induction i with
    | zero => intro x; exact ⟨(hG x).1, L, hLo, (hG x).2⟩
    | succ i ih =>
      intro x
      rw [Function.iterate_succ_apply']
      show (∑ y : X, actP w (phiMu h w μ e x y) ((matS h w μ e X)^[i] G y)) ∈ S ∧
        SmVec (pairRt a b w) (∑ y : X, actP w (phiMu h w μ e x y) ((matS h w μ e X)^[i] G y))
      exact ⟨Submodule.sum_mem _ fun y _ => (hGdAct x x.2 y y.2 _ (ih y).1 (ih y).2).1,
        smVec_sum _ _ fun y _ => (hGdAct x x.2 y y.2 _ (ih y).1 (ih y).2).2⟩

  have hrel : ∀ j, ∀ F : X → H E a b → ℂ, (∀ y, F y ∈ S ∧ SmVec (pairRt a b w) (F y)) → ∀ x : X,
      ∀ lw : Y →ₗ[ℂ] ℂ, lw (Λ j (matS h w μ e X F x)) =
        c₀ * ∑ y : X, hint (K2 a b w) (fun g => phi3 h w e x y g * lw (ρ g (Λ j (F y)))) := by
    intro j F hF x lw
    show lw (Λ j (∑ y : X, actP w (phiMu h w μ e x y) (F y))) = _
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    obtain ⟨U₁, hU₁o, hFU₁⟩ := (hF y).2
    have hFU : F y ∈ fixed (pairRt a b w) (U₁ ⊓ (Lv ⊓ χμ.ker)) :=
      mem_fixed_iff'.2 fun g hg => mem_fixed_iff'.1 hFU₁ g (Subgroup.mem_inf.1 hg).1
    rw [lw_actP w (U₁ ⊓ (Lv ⊓ χμ.ker)) (hU₁o.inter (hLvo.inter hχμo)) (F y) hFU (phiMu h w μ e x y) (hcs x y)
      (fun g k hk => hR x x.2 y y.2 g k (Subgroup.mem_inf.1 hk).2) τ (Λ j)
      (fun g => heq j g (F y) (hF y).1 (hF y).2) lw]
    rw [mul_comm, ← GlobalTheory.CompanionTheory.HeckeAct.hint_mul_const]
    congr 1
    funext g
    rw [hphiMu, hρτ, map_smul, smul_eq_mul]
    ring

  obtain ⟨x₀, hx₀⟩ : ∃ x : X, (matS h w μ e X)^[k + 1] G x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (funext hcon)
  obtain ⟨j, hj⟩ : ∃ j, Λ j ((matS h w μ e X)^[k + 1] G x₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx₀ (hsep _ (hGd _ x₀).1 (hGd _ x₀).2 hcon)

  let v : GLw n w → Y := fun y => if hy : y ∈ X then Λ j (G ⟨y, hy⟩) else 0
  have hv : ∀ y ∈ X, v y ∈ fixed ρ (L ⊓ χμ.ker) := by
    intro y hy
    refine mem_fixed_iff'.2 fun g hg => ?_
    have hGy : G ⟨y, hy⟩ ∈ fixed (pairRt a b w) L := (hG ⟨y, hy⟩).2
    simp only [v, dif_pos hy]
    rw [hρτ, ← heq j g _ (hG ⟨y, hy⟩).1 ⟨L, hLo, hGy⟩, mem_fixed_iff'.1 hGy g (Subgroup.mem_inf.1 hg).1,
      MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hg).2, Units.val_one, one_smul]
  obtain ⟨u₁, hu₁, hu₁x⟩ := key_ind h w K' hK'o hK'le hnorm X hXK hX ρ e hHk (L ⊓ χμ.ker) (hLo.inter hχμo) v hv
  have hTfix : ∀ i, (hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' e)^[i] u₁ ∈
      fixed (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' := by
    intro i
    induction i with
    | zero => exact hu₁
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact (((PositivityTheory.Rg.BcN.F2.Final.hkAlg _ _) K' e e hHk hHk).2.2 _ _ _ ih).1
  have hrun : ∀ i (x : X), Λ j ((matS h w μ e X)^[i + 1] G x) =
      c₀ ^ (i + 1) • ((hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' e)^[i] u₁).1.1 x := by
    intro i
    induction i with
    | zero =>
      intro x
      refine eq_of_dual fun lw => ?_
      rw [Function.iterate_one, hrel j G (fun y => hGd 0 y) x lw, map_smul, smul_eq_mul, pow_one,
        Function.iterate_zero_apply, hu₁x x x.2 lw, ← Finset.sum_coe_sort X]
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [v, dif_pos y.2]
    | succ i ih =>
      intro x
      refine eq_of_dual fun lw => ?_
      rw [Function.iterate_succ_apply', hrel j _ (fun y => hGd (i + 1) y) x lw, map_smul, smul_eq_mul,
        show (hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' e)^[i + 1] u₁ = hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' e
          ((hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' e)^[i] u₁) from Function.iterate_succ_apply' _ _ _,
        GlobalTheory.CompanionTheory.HeckeAct.hk_ind_apply E n a b h w K' hK'o hK'le hnorm X hXK hX _ ρ e hHk _ (hTfix i) x x.2 lw,
        ← Finset.sum_coe_sort X, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [ih y]
      have e4 : (fun g => phi3 h w e x y g * lw (ρ g (c₀ ^ (i + 1) •
          ((hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' e)^[i] u₁).1.1 y))) =
          fun g => (phi3 h w e x y g * lw (ρ g (((hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' e)^[i] u₁).1.1 y))) *
            c₀ ^ (i + 1) := by
        funext g
        rw [map_smul, map_smul, smul_eq_mul]
        ring
      rw [e4, GlobalTheory.CompanionTheory.HeckeAct.hint_mul_const, pow_succ]
      ring
  have hne₁ : (hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' e)^[k] u₁ ≠ 0 := by
    intro h0
    apply hj
    rw [hrun k x₀, h0]
    simp
  obtain ⟨hu₂, hne₂⟩ := transport _ π₂ Ψ K' e hHk u₁ hu₁ k hne₁
  exact ⟨Ψ u₁, hu₂, hne₂⟩

end PositivityTheory.Rg.BcB.F.Tail.PSc

namespace PositivityTheory.Rg.BcB.F.Tail

open PSc in
set_option maxHeartbeats 1000000 in
theorem rReadS_c : RReadS := by
  intro hRM hJM hLoc E _ _ _ n a b h μ s₁ s₂ Pa Pb D hC w K' X L e P m G hK'o hK'le hnorm hXK hX hLo hHk hkill hdim
    hG hne
  obtain ⟨hinv, J, Λ, heq, hsep⟩ := hRM E a b s₁ s₂ Pa Pb w hC.g₁ hC.g₂ hC.u₁ hC.u₂ hC.t₁ hC.t₂
  obtain ⟨Φ⟩ := hJM E n a b h (μ ^ b) (μ ^ a) Pa Pb D w hC.join
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact Nat.not_lt_zero _ hdim
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := Nat.exists_eq_succ_of_ne_zero hm0
  obtain ⟨u, hu, hne'⟩ := core h w (μ.loc w) (pairSpace s₁.space s₂.space) hinv
    (GlobalTheory.SmGL.extTensor (lp Pa w) (lp Pb w))
    (GlobalTheory.SmGL.extTensor (twRep (lp Pa w) (((μ ^ b).loc w).comp GeneralLinearGroup.det))
      (twRep (lp Pb w) (((μ ^ a).loc w).comp GeneralLinearGroup.det))) Λ heq hsep (chiMu μ w a b)
    (isOpen_chiMu μ w a b) (fun g v => tw_eq (lp Pa w) (lp Pb w) μ g v) _ e (fun x y g => phiMu_eq h w μ e x y g)
    K' hK'o hK'le hnorm X hXK hX hHk L hLo G hG k hne (lp D w) Φ.symm
  exact sub_of_pow D w K' e hHk P hkill (k + 1) hdim u hu hne'

end PositivityTheory.Rg.BcB.F.Tail

end
