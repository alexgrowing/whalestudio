import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RepAtTup
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.TupOrb

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def rAct {n : ℕ} (β : Matrix (Fin n) (Fin n) E) (f : Fin n → S.V) : Fin n → S.V :=
  fun a => ∑ c, β a c • f c

theorem rAct_map {n : ℕ} (β : Matrix (Fin n) (Fin n) E) (f : Fin n → S.V) (k : S.V ≃ₗ[E] S.V) :
    rAct β (fun c => k (f c)) = fun a => k (rAct β f a) := by
  funext a
  simp [rAct, map_sum, map_smul]

theorem rAct_mul {n : ℕ} (α β : Matrix (Fin n) (Fin n) E) (f : Fin n → S.V) :
    rAct α (rAct β f) = rAct (α * β) f := by
  funext a
  simp only [rAct, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem rAct_one {n : ℕ} (f : Fin n → S.V) : rAct (1 : Matrix (Fin n) (Fin n) E) f = f := by
  funext a
  simp [rAct, Matrix.one_apply, ite_smul]

theorem det_uni {n : ℕ} (β : Matrix (Fin n) (Fin n) E) (h0 : ∀ a c, a < c → β a c = 0) (h1 : ∀ a, β a a = 1) :
    β.det = 1 := by
  rw [Matrix.det_of_lowerTriangular β (fun i j hij => h0 i j (by simpa using hij))]
  simp [h1]

theorem rAct_inj {n : ℕ} {β : Matrix (Fin n) (Fin n) E} (h0 : ∀ a c, a < c → β a c = 0) (h1 : ∀ a, β a a = 1)
    {f f' : Fin n → S.V} (h : rAct β f = rAct β f') : f = f' := by
  have hd : IsUnit β.det := by rw [det_uni β h0 h1]; exact isUnit_one
  have h' := congrArg (rAct β⁻¹) h
  rwa [rAct_mul, rAct_mul, Matrix.nonsing_inv_mul _ hd, rAct_one, rAct_one] at h'

theorem frameAct_one' {n : ℕ} (f : Fin n → S.V) (b : Fin n) :
    frameAct f (1 : Matrix (Fin n) (Fin n) (𝓞 E)) b = f b := by
  simp [frameAct, Matrix.one_apply, apply_ite]

theorem modG_move {g : ℕ} {Λ : Submodule (𝓞 E) S.V} {T T' : E} {F : LFlag S r T} {F₁ F'' F₂ : LFlag S r T'}
    (hL : IsLift Λ F₁) (hC : IsFixedConv Λ g F₁)
    {n m k : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) (hm : m ∈ NLam Λ F₁)
    (hk : ∀ c, k (frame F₁ c) = frame F'' c)
    (h1 : ∀ c, ModG S Λ g (frame F₁ c - frame F c)) (h'' : ∀ c, ModG S Λ g (frame F'' c - frame F c))
    (h2 : ∀ c, ModG S Λ g (frame F₂ c - frame F c)) (hfr : ∀ c, frame F₂ c = n (m (frame F₁ c)))
    (b : Fin (r + 1)) : ModG S Λ g (n (k (m (frame F₁ b))) - frame F b) := by
  intro P hg
  have := P.isPrime
  have hi : ∀ c, k (frame F₁ c) - frame F₁ c ∈
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) := fun c => by
    rw [hk c]
    have := Submodule.sub_mem _ (h'' c P hg) (h1 c P hg)
    rwa [sub_sub_sub_cancel_right] at this
  have hii : ∀ v ∈ Submodule.span (𝓞 E) (Set.range (frame F₁)),
      k v - v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact hi c
    | zero => simp
    | add x y _ _ hx hy =>
      have := Submodule.add_mem _ hx hy
      rwa [map_add, add_sub_add_comm]
    | smul o x _ hx =>
      rw [Formalism.L2.SG.Pf.smul_O, map_smul, ← smul_sub, ← Formalism.L2.SG.Pf.smul_O]
      exact Submodule.smul_mem _ o hx
  have hA : Formalism.L2.SG.Pf.Apart Λ F₁ ≤
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 E) (Set.range (frame F₁))) := by
    refine sup_le ?_ ?_
    · exact Formalism.L2.SG.Pf.Act.xlam_le_locP Λ g hC P hg (fun a =>
        Formalism.L2.SG.Pf.le_locP' _ _ (Submodule.subset_span ⟨a.castSucc, Formalism.L2.SG.Pf.frame_castSucc_td F₁ a⟩))
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Formalism.L2.SG.Pf.le_locP' _ _
        (Submodule.subset_span ⟨Fin.last _, (Formalism.L2.SG.Pf.frame_last_td F₁).trans hL.2.symm⟩)
  have hy : m (frame F₁ b) ∈
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 E) (Set.range (frame F₁))) := by
    have h0 := Formalism.L2.SG.Pf.frame_mem_locP_Apart hL hC P hg b
    have h1' : m (frame F₁ b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.L2.SG.Pf.Apart Λ F₁) := by
      rw [← Formalism.L2.SG.Pf.NLam_Apart hm hL, Formalism.L2.SG.Pf.gmap_locP]
      exact (Formalism.L2.SG.Pf.gmap_apply_mem m _ _).2 h0
    exact Formalism.L2.SG.Pf.locP_le_locP' hA h1'
  have hiv : k (m (frame F₁ b)) - m (frame F₁ b) ∈
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) := by
    obtain ⟨s, hs, hsy⟩ := hy
    have := hii _ hsy
    rw [Formalism.L2.SG.Pf.smul_O, map_smul, ← smul_sub, ← Formalism.L2.SG.Pf.smul_O] at this
    obtain ⟨t, ht, htx⟩ := this
    exact ⟨t * s, P.asIdeal.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact htx⟩
  have hv : n (k (m (frame F₁ b)) - m (frame F₁ b)) ∈
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) := by
    have e : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) =
        Formalism.HermitianLatticesTheory.gmap n (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ)) := by
      rw [← Formalism.L2.SG.Pf.gmap_locP, Formalism.L2.SG.Pf.gmap_ideal_smul, hn.2]
    rw [e]
    exact (Formalism.L2.SG.Pf.gmap_apply_mem n _ _).2 hiv
  have e : n (k (m (frame F₁ b))) - frame F b =
      n (k (m (frame F₁ b)) - m (frame F₁ b)) + (frame F₂ b - frame F b) := by
    rw [hfr b, map_sub]; abel
  rw [e]
  exact Submodule.add_mem _ hv (h2 b P hg)

theorem zhat_move {Λ : Submodule (𝓞 E) S.V} {T : E} (F : LFlag S r T) {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F)
    (β : Matrix (Fin (r + 1)) (Fin (r + 1)) E) {f f' : Fin (r + 1) → S.V}
    (h : ∀ e d, S.hT (frame F e) (f d) = S.hT (frame F e) (f' d)) (a b : Fin (r + 1)) :
    S.hT (frame F a) (n (rAct β f b)) = S.hT (frame F a) (n (rAct β f' b)) := by
  have hni : n⁻¹ ∈ NLam Λ F := Pf.nlamPf_inv hn
  have hspan : ∀ x ∈ Xsp F, ∀ d, S.hT x (f d) = S.hT x (f' d) := by
    intro x hx
    have hx' : x ∈ Submodule.span E (Set.range F.fl.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      intro d
      simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using h i.castSucc d
    | zero => intro d; simp
    | add x y _ _ hx hy => intro d; simp [hx d, hy d]
    | smul c x _ hx => intro d; simp [hx d]
  have hw : ∀ a', n.symm (frame F a') - frame F a' ∈ Xsp F := by
    intro a'
    refine Fin.lastCases ?_ (fun i => ?_) a'
    · have := hni.2.2 _ (Pf.isotropicSpan_orthogonal_anisotropicVector F)
      simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using this
    · have h1 : F.fl.e i ∈ Xflag F (i.1 + 1) := Submodule.subset_span ⟨i, by simp, rfl⟩
      have := Submodule.span_mono (Set.image_subset_range _ _) (hni.2.1 i.1 _ h1)
      simp only [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
      exact this
  have key : ∀ c, S.hT (n.symm (frame F a)) (f c) = S.hT (n.symm (frame F a)) (f' c) := by
    intro c
    have e1 : n.symm (frame F a) = frame F a + (n.symm (frame F a) - frame F a) := by abel
    rw [e1, map_add, LinearMap.add_apply, LinearMap.add_apply, h a c, hspan _ (hw a) c]
  calc S.hT (frame F a) (n (rAct β f b))
      = S.hT (n (n.symm (frame F a))) (n (rAct β f b)) := by rw [n.apply_symm_apply]
    _ = S.hT (n.symm (frame F a)) (rAct β f b) := Saturated.isom_apply hn.1.1 _ _
    _ = S.hT (n.symm (frame F a)) (rAct β f' b) := by
      simp only [rAct, map_sum, map_smul]
      exact Finset.sum_congr rfl (fun c _ => by rw [key c])
    _ = S.hT (n (n.symm (frame F a))) (n (rAct β f' b)) := (Saturated.isom_apply hn.1.1 _ _).symm
    _ = S.hT (frame F a) (n (rAct β f' b)) := by rw [n.apply_symm_apply]

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem flagStabilizer_inv_mem {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : n ∈ CntLocal.N0 F0 Λ) : n⁻¹ ∈ CntLocal.N0 F0 Λ := by
  obtain ⟨hN, he, hz⟩ := h
  refine ⟨Pf.nlamPf_inv hN, fun a => ?_, ?_⟩
  · show n.symm _ = _
    rw [LinearEquiv.symm_apply_eq]
    exact (he a).symm
  · show n.symm _ = _
    rw [LinearEquiv.symm_apply_eq]
    exact hz.symm

theorem flagStabilizer_mul_mem {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {n k : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : n ∈ CntLocal.N0 F0 Λ) (h' : k ∈ CntLocal.N0 F0 Λ) :
    n * k ∈ CntLocal.N0 F0 Λ := by
  obtain ⟨hN, he, hz⟩ := h
  obtain ⟨hN', he', hz'⟩ := h'
  refine ⟨PI.DCRelEquiv.UnitaryGroupMassFormula.nlam_mul hN hN', fun a => ?_, ?_⟩
  · show n (k _) = _
    rw [he', he]
  · show n (k _) = _
    rw [hz', hz]

theorem flagStabilizer_fixes_frame {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {k : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : k ∈ CntLocal.N0 F0 Λ) (c : Fin (D.R.rS + 1)) :
    k (frame (lf D F0) c) = frame (lf D F0) c := by
  obtain ⟨_, he, hz⟩ := h
  refine Fin.lastCases ?_ (fun i => ?_) c
  · simpa [frame, Formalism.MainNotions.S.FlagG.fvec, lf] using hz
  · simpa [frame, Formalism.MainNotions.S.FlagG.fvec, lf] using he i

theorem n0rel_iff {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {F' F'' : LFlag (VS D) D.R.rS T'} :
    CntLocal.NilradicalFlagMoved F0 Λ F' F'' ↔ ∃ n ∈ CntLocal.N0 F0 Λ, ∀ c, n (frame F' c) = frame F'' c := by
  constructor
  · rintro ⟨n, hn, he, hz⟩
    refine ⟨n, hn, fun c => ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_) c
    · simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using hz
    · simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using he i
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, fun a => by simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using h a.castSucc,
      by simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using h (Fin.last _)⟩

theorem n0rel_symm {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {F' F'' : LFlag (VS D) D.R.rS T'} (h : CntLocal.NilradicalFlagMoved F0 Λ F' F'') : CntLocal.NilradicalFlagMoved F0 Λ F'' F' := by
  obtain ⟨n, hn, he, hz⟩ := h
  refine ⟨n⁻¹, flagStabilizer_inv_mem hn, fun a => ?_, ?_⟩
  · show n.symm _ = _
    rw [LinearEquiv.symm_apply_eq]
    exact (he a).symm
  · show n.symm _ = _
    rw [LinearEquiv.symm_apply_eq]
    exact hz.symm

theorem n0rel_trans {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {F₁ F₂ F₃ : LFlag (VS D) D.R.rS T'} (h : CntLocal.NilradicalFlagMoved F0 Λ F₁ F₂) (h' : CntLocal.NilradicalFlagMoved F0 Λ F₂ F₃) :
    CntLocal.NilradicalFlagMoved F0 Λ F₁ F₃ := by
  obtain ⟨n, hn, he, hz⟩ := h
  obtain ⟨k, hk, he', hz'⟩ := h'
  refine ⟨k * n, flagStabilizer_mul_mem hk hn, fun a => ?_, ?_⟩
  · show k (n _) = _
    rw [he, he']
  · show k (n _) = _
    rw [hz, hz']

theorem flagStabilizer_conj_mem {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {n k : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam Λ (lf D F0)) (hk : k ∈ CntLocal.N0 F0 Λ) :
    n⁻¹ * k * n ∈ CntLocal.N0 F0 Λ := by
  obtain ⟨hN, he, hz⟩ := hk
  have hfix : ∀ x ∈ Xsp (lf D F0), k x = x := by
    intro x hx
    have h := LinearMap.eqOn_span' (f := k.toLinearMap) (g := LinearMap.id)
      (s := Set.range F0.e) (by rintro _ ⟨a, rfl⟩; simpa using he a)
    exact h hx
  have key : ∀ x, k x = x → n x - x ∈ Xsp (lf D F0) → (n⁻¹ * k * n) x = x := by
    intro x hx hw
    have hnx : k (n x) = n x := by
      have e1 : n x = x + (n x - x) := by abel
      rw [e1, map_add, hx, hfix _ hw]
    show n.symm (k (n x)) = x
    rw [hnx]
    exact n.symm_apply_apply x
  refine ⟨PI.DCRelEquiv.UnitaryGroupMassFormula.nlam_mul (PI.DCRelEquiv.UnitaryGroupMassFormula.nlam_mul (Pf.nlamPf_inv hn) hN) hn,
    fun a => key _ (he a) ?_, key _ hz ?_⟩
  · have h1 : F0.e a ∈ Xflag (lf D F0) (a.1 + 1) :=
      Submodule.subset_span ⟨a, by simp, rfl⟩
    exact Submodule.span_mono (Set.image_subset_range _ _) (hn.2.1 a.1 _ h1)
  · exact hn.2.2 _ (Pf.isotropicSpan_orthogonal_anisotropicVector (lf D F0))

theorem n0rel_pull {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam Λ (lf D F0))
    {β : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E} (h0 : ∀ a c, a < c → β a c = 0)
    (h1 : ∀ a, β a a = 1) {a b a' b' : LFlag (VS D) D.R.rS T'}
    (ha : ∀ c, frame a' c = n (rAct β (frame a) c)) (hb : ∀ c, frame b' c = n (rAct β (frame b) c))
    (h : CntLocal.NilradicalFlagMoved F0 Λ a' b') : CntLocal.NilradicalFlagMoved F0 Λ a b := by
  rw [n0rel_iff] at h ⊢
  obtain ⟨k, hk, hkc⟩ := h
  refine ⟨n⁻¹ * k * n, flagStabilizer_conj_mem hn hk, ?_⟩
  have h2 : rAct β (fun c => (n⁻¹ * k * n) (frame a c)) = rAct β (frame b) := by
    rw [rAct_map]
    funext c
    show n.symm (k (n (rAct β (frame a) c))) = rAct β (frame b) c
    rw [← ha c, hkc c, hb c]
    exact n.symm_apply_apply _
  intro c
  exact congrFun (rAct_inj h0 h1 h2) c

theorem n0rel_refl' {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (F' : LFlag (VS D) D.R.rS T') : CntLocal.NilradicalFlagMoved F0 Λ F' F' :=
  ⟨1, ⟨TermDef.one_mem_NLam (Λ := Λ) _, fun _ => rfl, rfl⟩, fun _ => rfl, rfl⟩

section Move

variable (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (Λ : Submodule (𝓞 D.host.E) (VS D).V)

def orbS (t : TermsOf D u' F0 Λ) (Z : PairVal.MatR D) :
    Set (Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))) :=
  {O | ∃ F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z,
    TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F' ∧
    O = {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z ∧ CntLocal.NilradicalFlagMoved F0 Λ F' F''}}

variable {u u' F0 Λ}

theorem move_exists (hΛ : IsRowLat D F0 Λ) {t : TermsOf D u' F0 Λ} {Z₁ Z₂ : PairVal.MatR D}
    {F₁ F₂ F'' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    (h₁ : F₁ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z₁)
    (h₂ : F₂ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z₂)
    (r₁ : TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F₁)
    {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam Λ (lf D F0)) (hm : m ∈ NLam Λ F₁)
    (hfr : ∀ a, frame F₂ a = n (m (frame F₁ a)))
    {β : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E}
    (hβ : ∀ a, m (frame F₁ a) = ∑ c, β a c • frame F₁ c)
    (h'' : F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z₁)
    (r'' : TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F'') :
    ∃ F3 ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z₂,
      TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F3 ∧ ∀ a, frame F3 a = n (rAct β (frame F'') a) := by
  obtain ⟨p₁, e₁⟩ := r₁
  obtain ⟨p'', e''⟩ := r''
  obtain ⟨n'', hn'', m'', hm'', hfr'', -⟩ :=
    (Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 Λ hΛ ⟨F₁, p₁⟩ ⟨F'', p''⟩).1 (e₁.trans e''.symm)
  have hgA : IsAutLam (VS D) Λ (n * n'' * (m'' * m)) :=
    Formalism.L2.SG.Pf.isAutLam_mul (Formalism.L2.SG.Pf.isAutLam_mul hn.1 hn''.1)
      (Formalism.L2.SG.Pf.isAutLam_mul hm''.1 hm.1)
  let F3 := Formalism.L2.SG.Saturated.mapL (n * n'' * (m'' * m)) hgA.1 F₁
  have hf3 : ∀ a, frame F3 a = n (n'' (m'' (m (frame F₁ a)))) := fun a => by
    rw [Formalism.L2.SG.Saturated.frame_mapL]; rfl
  have hdc : DCRel Λ (lf D F0) F₁ F3 :=
    ⟨n * n'', Formalism.L2.SG.Pf.nlamPf_mul hn hn'', m'' * m, Formalism.L2.SG.Pf.nlamPf_mul hm'' hm,
      fun a => by rw [hf3 a]; rfl, rfl⟩
  have hframe : ∀ a, frame F3 a = n (rAct β (frame F'') a) := fun a => by
    rw [hf3 a, hβ a]
    simp only [rAct, map_sum, map_smul, hfr'']
  have pd3 : PD D Λ (lf D F0) u' F3 :=
    Formalism.L2.SG.Closed.TermStable_holds D u u' F0 Λ hΛ ⟨F₁, p₁⟩ F3 hdc
  have hrep : TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F3 :=
    ⟨pd3, (Quot.sound (show TermDef.Rel Λ (lf D F0) (PD D Λ (lf D F0) u') ⟨F₁, p₁⟩ ⟨F3, pd3⟩ from hdc)).symm.trans e₁⟩
  have hF₂ : ∀ a, frame F₂ a = n (rAct β (frame F₁) a) := fun a => by rw [hfr a, hβ a]; rfl
  have hent : ∀ a b, (VS D).hT (frame (lf D F0) a) (frame F3 b) = (VS D).hT (frame (lf D F0) a) (frame F₂ b) := by
    intro a b
    have hZ : ∀ e d, (VS D).hT (frame (lf D F0) e) (frame F'' d) =
        (VS D).hT (frame (lf D F0) e) (frame F₁ d) := by
      intro e d
      have := congrArg (fun M : PairVal.MatR D => M e d) (h''.2.2.2.2.trans h₁.2.2.2.2.symm)
      simpa [ZhatL, Zhat, brS] using this
    rw [hframe b, hF₂ b]
    exact zhat_move (lf D F0) hn β hZ a b
  have hent : ∀ a b, (VS D).hT (frame (lf D F0) a) (frame F3 b) =
      (VS D).hT (frame (lf D F0) a) (frame F₂ b) := by
    intro a b
    have hZ : ∀ e d, (VS D).hT (frame (lf D F0) e) (frame F'' d) =
        (VS D).hT (frame (lf D F0) e) (frame F₁ d) := by
      intro e d
      have := congrArg (fun M : PairVal.MatR D => M e d) (h''.2.2.2.2.trans h₁.2.2.2.2.symm)
      simpa [ZhatL, Zhat, brS] using this
    rw [hframe b, hF₂ b]
    exact zhat_move (lf D F0) hn β hZ a b
  refine ⟨F3, ⟨⟨pd3.1, pd3.2.1, ?_⟩, ?_, ?_, pd3.2.2, ?_⟩, hrep, hframe⟩
  · rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hdc]; exact h₁.1.2.2
  · refine ⟨fun a b hab => Matrix.one_apply_ne (ne_of_lt hab).symm, fun a => Matrix.one_apply_eq a, fun b => ?_⟩
    rw [frameAct_one']
    have hk : ∀ c, (n'' * m'') (frame F₁ c) = frame F'' c := fun c => by
      rw [hfr'' c]; rfl
    have e3 : frame F3 b = n ((n'' * m'') (m (frame F₁ b))) := by rw [hf3 b]; rfl
    rw [e3]
    refine modG_move h₁.1.1 h₁.2.2.2.1.1 hn.1 hm hk (fun c => ?_) (fun c => ?_) (fun c => ?_) hfr b
    · have := h₁.2.1.2.2 c; rwa [frameAct_one'] at this
    · have := h''.2.1.2.2 c; rwa [frameAct_one'] at this
    · have := h₂.2.1.2.2 c; rwa [frameAct_one'] at this
  · exact ((Formalism.L2.SG.Closed.TermFun_holds D u u' F0 Λ hΛ).2.2.2.1 ⟨F₁, p₁⟩ ⟨F3, pd3⟩ hdc).1 h₁.2.2.1
  · have hZZ : ZhatL (lf D F0) F3 = ZhatL (lf D F0) F₂ := by
      funext a b
      exact hent a b
    rw [← h₂.2.2.2.2]
    exact hZZ

theorem orb_le (hΛ : IsRowLat D F0 Λ) {t : TermsOf D u' F0 Λ} {Z₁ Z₂ : PairVal.MatR D}
    {F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    (h₁ : F₁ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z₁)
    (h₂ : F₂ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z₂)
    (r₁ : TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F₁)
    (r₂ : TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F₂) :
    (orbS u u' F0 Λ t Z₁).encard ≤ (orbS u u' F0 Λ t Z₂).encard := by
  obtain ⟨p₁, e₁⟩ := r₁
  obtain ⟨p₂, e₂⟩ := r₂
  obtain ⟨n, hn, m, hm, hfr, -⟩ :=
    (Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 Λ hΛ ⟨F₁, p₁⟩ ⟨F₂, p₂⟩).1 (e₁.trans e₂.symm)
  obtain ⟨β, hβ0, hβ1, hβ⟩ := Formalism.L2.SG.Pf.nlam_coef hm
  have mv : ∀ F'' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E),
      F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z₁ ∧
        TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F'' →
      ∃ F3, F3 ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z₂ ∧
        TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F3 ∧ ∀ a, frame F3 a = n (rAct β (frame F'') a) :=
    fun F'' h => move_exists hΛ h₁ h₂ ⟨p₁, e₁⟩ hn hm hfr hβ h.1 h.2
  choose G hG using mv
  have rp : ∀ O, O ∈ orbS u u' F0 Λ t Z₁ → ∃ F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E),
      F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z₁ ∧
      TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F' ∧
      O = {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z₁ ∧ CntLocal.NilradicalFlagMoved F0 Λ F' F''} :=
    fun O hO => hO
  choose R hR using rp
  refine Set.encard_le_encard_of_injOn (f := fun O => if hO : O ∈ orbS u u' F0 Λ t Z₁ then
      {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z₂ ∧
        CntLocal.NilradicalFlagMoved F0 Λ (G (R O hO) ⟨(hR O hO).1, (hR O hO).2.1⟩) F''} else ∅) ?_ ?_
  · intro O hO
    dsimp only
    rw [dif_pos hO]
    have hs := hG (R O hO) ⟨(hR O hO).1, (hR O hO).2.1⟩
    exact ⟨_, hs.1, hs.2.1, rfl⟩
  · intro O₁ hO₁ O₂ hO₂ he
    dsimp only at he
    rw [dif_pos hO₁, dif_pos hO₂] at he
    have ha := hG (R O₁ hO₁) ⟨(hR O₁ hO₁).1, (hR O₁ hO₁).2.1⟩
    have hb := hG (R O₂ hO₂) ⟨(hR O₂ hO₂).1, (hR O₂ hO₂).2.1⟩
    have hmem := (Set.ext_iff.1 he (G (R O₂ hO₂) ⟨(hR O₂ hO₂).1, (hR O₂ hO₂).2.1⟩)).2 ⟨hb.1, n0rel_refl' Λ _⟩
    have hab := n0rel_pull hn hβ0 hβ1 ha.2.2 hb.2.2 hmem.2
    rw [(hR O₁ hO₁).2.2, (hR O₂ hO₂).2.2]
    ext x
    constructor
    · rintro ⟨hx, hax⟩
      exact ⟨hx, n0rel_trans (n0rel_symm hab) hax⟩
    · rintro ⟨hx, hbx⟩
      exact ⟨hx, n0rel_trans hab hbx⟩

theorem orb_eq (hΛ : IsRowLat D F0 Λ) {t : TermsOf D u' F0 Λ} {Z₁ Z₂ : PairVal.MatR D}
    {F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    (h₁ : F₁ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z₁)
    (h₂ : F₂ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z₂)
    (r₁ : TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F₁)
    (r₂ : TermDef.Rep Λ (lf D F0) (PD D Λ (lf D F0) u') t F₂) :
    (orbS u u' F0 Λ t Z₁).encard = (orbS u u' F0 Λ t Z₂).encard :=
  le_antisymm (orb_le hΛ h₁ h₂ r₁ r₂) (orb_le hΛ h₂ h₁ r₂ r₁)

end Move

theorem orbZT_holds (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) :
    FibPart.OrbZT M δ u u' F0 what₂ := by
  intro hpre γ w Z _ hAt hR
  obtain ⟨F₁, h₁, r₁⟩ := hR
  have hΛ : IsRowLat D F0 γ.lam := hpre.2.2.2.2.1.1 γ.lam γ.mem
  obtain ⟨L, U, hL, hU, he⟩ := hAt
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) ×
      PairVal.MatR D × PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 :=
    ⟨(w, F₁, L, U), r₁, h₁.2.1, hL, hU, (congrArg ZhatOM h₁.2.2.2.2).trans he⟩
  have hz : LsDatumB.zT γ = ZhatL (lf D F0) hex.choose.2.1 := by
    simp only [LsDatumB.zT, LsDatumB.nrep, dif_pos hex]
  obtain ⟨r₂, hadm, -⟩ := hex.choose_spec
  obtain ⟨p₁, e₁⟩ := r₁
  obtain ⟨p₂, e₂⟩ := r₂
  have hdc := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 γ.lam hΛ ⟨F₁, p₁⟩ ⟨_, p₂⟩).1 (e₁.trans e₂.symm)
  have h₂ : hex.choose.2.1 ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam
      (ZhatL (lf D F0) hex.choose.2.1) :=
    ⟨⟨p₂.1, p₂.2.1, by rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hdc]; exact h₁.1.2.2⟩, hadm,
      ((Formalism.L2.SG.Closed.TermFun_holds D u u' F0 γ.lam hΛ).2.2.2.1 ⟨F₁, p₁⟩ ⟨_, p₂⟩ hdc).1 h₁.2.2.1, p₂.2.2, rfl⟩
  rw [hz]
  exact orb_eq hΛ h₂ h₁ ⟨p₂, e₂⟩ ⟨p₁, e₁⟩

end D7

end Formalism.L2.SG.Pf.TupOrb
