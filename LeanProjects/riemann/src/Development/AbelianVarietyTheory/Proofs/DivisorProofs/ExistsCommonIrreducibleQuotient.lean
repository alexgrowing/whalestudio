import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
open GlobalTheory.FockAlg (genSub)

noncomputable section

namespace GlobalTheory.CommonQuot

variable {p q : ℕ}

section General

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem mem_hwSub' (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub act μ ↔ (∀ a, act (Eab a a) v - ((μ a : ℚ) : ℂ) • v = 0) ∧
      ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]

theorem isKC_diag' (a : Ix p q) : IsKC (Eab a a) := by
  intro c d h
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  cases a <;> simp [sameBlock] at h

theorem isKC_pos' {a b : Ix p q} (hab : posC a b) : IsKC (Eab a b) := by
  intro c d h
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  cases a <;> cases b <;> simp_all [sameBlock, posC]

theorem map_hw {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (g : V →ₗ[ℂ] V') (hg : ∀ Z v, g (a Z v) = b Z (g v)) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ hwSub a μ) : g v ∈ hwSub b μ := by
  rw [mem_hwSub'] at hv ⊢
  refine ⟨fun c => ?_, fun c d h => ?_⟩
  · rw [← hg, ← map_smul, ← map_sub, hv.1 c, map_zero]
  · rw [← hg, hv.2 c d h, map_zero]

theorem hw_of_inj {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (g : V →ₗ[ℂ] V') (hg : ∀ Z v, g (a Z v) = b Z (g v)) (hinj : Function.Injective g)
    {μ : Ix p q → ℚ} {u : V} (h : g u ∈ hwSub b μ) : u ∈ hwSub a μ := by
  rw [mem_hwSub'] at h ⊢
  refine ⟨fun c => hinj ?_, fun c d hcd => hinj ?_⟩
  · rw [map_sub, map_smul, hg, map_zero]; exact h.1 c
  · rw [hg, map_zero]; exact h.2 c d hcd

theorem map_wts {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (g : V →ₗ[ℂ] V') (hg : ∀ Z v, g (a Z v) = b Z (g v)) {x : V}
    (hx : x ∈ ⨆ μ : Ix p q → ℚ, wtSub a μ) : g x ∈ ⨆ μ : Ix p q → ℚ, wtSub b μ := by
  refine Submodule.iSup_induction _ (motive := fun v => g v ∈ _) hx ?_ (by simp) ?_
  · intro μ y hy
    refine Submodule.mem_iSup_of_mem μ ?_
    simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
    intro c
    rw [← hg, ← map_smul, ← map_sub, hy c, map_zero]
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy

theorem eq_zero_of_add {A B : Submodule ℂ V} (h : A ⊓ B = ⊥) {x y : V} (hx : x ∈ A) (hy : y ∈ B)
    (hxy : x + y = 0) : x = 0 ∧ y = 0 := by
  have hx' : x ∈ B := by
    rw [eq_neg_of_add_eq_zero_left hxy]; exact B.neg_mem hy
  have h0 : x = 0 := by
    have : x ∈ A ⊓ B := ⟨hx, hx'⟩
    rw [h] at this; exact (Submodule.mem_bot ℂ).1 this
  refine ⟨h0, ?_⟩
  rw [h0, zero_add] at hxy; exact hxy

theorem split_hw {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {A B : Submodule ℂ V}
    (hA : KStable a A) (hB : KStable a B) (hAB : A ⊓ B = ⊥) {μ : Ix p q → ℚ} {y z : V}
    (hy : y ∈ A) (hz : z ∈ B) (h : y + z ∈ hwSub a μ) : y ∈ hwSub a μ ∧ z ∈ hwSub a μ := by
  rw [mem_hwSub'] at h
  rw [mem_hwSub', mem_hwSub']
  obtain ⟨h1, h2⟩ := h
  have e1 : ∀ c, (a (Eab c c) y - ((μ c : ℚ) : ℂ) • y) = 0 ∧
      (a (Eab c c) z - ((μ c : ℚ) : ℂ) • z) = 0 := by
    intro c
    refine eq_zero_of_add hAB (A.sub_mem (hA _ (isKC_diag' c) y hy) (A.smul_mem _ hy))
      (B.sub_mem (hB _ (isKC_diag' c) z hz) (B.smul_mem _ hz)) ?_
    have := h1 c
    rw [map_add, smul_add] at this
    rw [← this]; abel
  have e2 : ∀ c d, posC c d → a (Eab c d) y = 0 ∧ a (Eab c d) z = 0 := by
    intro c d hcd
    refine eq_zero_of_add hAB (hA _ (isKC_pos' hcd) y hy) (hB _ (isKC_pos' hcd) z hz) ?_
    rw [← map_add]; exact h2 c d hcd
  exact ⟨⟨fun c => (e1 c).1, fun c d hcd => (e2 c d hcd).1⟩,
    ⟨fun c => (e1 c).2, fun c d hcd => (e2 c d hcd).2⟩⟩

theorem hw_sup {a : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsKLieAct a)
    (hwts : ∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub a μ) {μ : Ix p q → ℚ} {U W : Submodule ℂ V}
    [FiniteDimensional ℂ W] (sU : KStable a U) (sW : KStable a W) {v : V} (hv : v ∈ U ⊔ W)
    (h : v ∈ hwSub a μ) : ∃ y ∈ U, ∃ z ∈ W, y ∈ hwSub a μ ∧ z ∈ hwSub a μ ∧ y + z = v := by
  obtain ⟨C, sC, hUC, hUCW⟩ := GlobalTheory.BlockReps.exists_compl hL sW (fun v _ => hwts v) (U ⊓ W)
    inf_le_right (GlobalTheory.BlockReps.stable_inf sU sW)
  have hCW : C ≤ W := by rw [← hUCW]; exact le_sup_right
  have hdisj : U ⊓ C = ⊥ := by
    rw [eq_bot_iff]; rintro x ⟨hxU, hxC⟩
    have : x ∈ (U ⊓ W) ⊓ C := ⟨⟨hxU, hCW hxC⟩, hxC⟩
    rwa [hUC] at this
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
  have hw' : w ∈ (U ⊓ W) ⊔ C := by rw [hUCW]; exact hw
  obtain ⟨w1, hw1, c, hc, rfl⟩ := Submodule.mem_sup.1 hw'
  have hsum : (u + w1) + c = u + (w1 + c) := add_assoc _ _ _
  rw [← hsum] at h
  obtain ⟨h1, h2⟩ := split_hw sU sC hdisj (U.add_mem hu hw1.1) hc h
  exact ⟨u + w1, U.add_mem hu hw1.1, c, hCW hc, h1, h2, hsum⟩

theorem hw_lift {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (hL : IsKLieAct a) (hwts : ∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub a μ)
    (g : V →ₗ[ℂ] V') (hg : ∀ Z v, g (a Z v) = b Z (g v)) {μ : Ix p q → ℚ}
    {W : Submodule ℂ V} [FiniteDimensional ℂ W] (sW : KStable a W) {w : V} (hw : w ∈ W)
    (h : g w ∈ hwSub b μ) : ∃ u ∈ hwSub a μ, g u = g w := by
  have sK : KStable a (W ⊓ LinearMap.ker g) := GlobalTheory.BlockReps.stable_inf sW (fun Z _ y hy => by
    rw [LinearMap.mem_ker] at hy ⊢; rw [hg, hy, map_zero])
  obtain ⟨C, sC, hKC, hKCW⟩ := GlobalTheory.BlockReps.exists_compl hL sW (fun v _ => hwts v)
    (W ⊓ LinearMap.ker g) inf_le_left sK
  have hw' : w ∈ (W ⊓ LinearMap.ker g) ⊔ C := by rw [hKCW]; exact hw
  obtain ⟨k, hk, c, hc, rfl⟩ := Submodule.mem_sup.1 hw'
  have hgc : g c = g (k + c) := by rw [map_add, LinearMap.mem_ker.1 hk.2, zero_add]
  have hCW : C ≤ W := by rw [← hKCW]; exact le_sup_right
  have inj : ∀ x ∈ C, g x = 0 → x = 0 := by
    intro x hx hgx
    have : x ∈ (W ⊓ LinearMap.ker g) ⊓ C := ⟨⟨hCW hx, hgx⟩, hx⟩
    rw [hKC] at this; exact (Submodule.mem_bot ℂ).1 this
  refine ⟨c, ?_, hgc⟩
  rw [← hgc] at h
  rw [mem_hwSub'] at h ⊢
  refine ⟨fun i => inj _ (C.sub_mem (sC _ (isKC_diag' i) c hc) (C.smul_mem _ hc)) ?_,
    fun i j hij => inj _ (sC _ (isKC_pos' hij) c hc) ?_⟩
  · rw [map_sub, map_smul, hg]; exact h.1 i
  · rw [hg]; exact h.2 i j hij

theorem exists_factor {A B C : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] (f : A →ₗ[ℂ] B) (hf : Function.Surjective f) (g : A →ₗ[ℂ] C)
    (h : LinearMap.ker f ≤ LinearMap.ker g) : ∃ π : B →ₗ[ℂ] C, ∀ x, π (f x) = g x := by
  refine ⟨(LinearMap.ker f).liftQ g h ∘ₗ (f.quotKerEquivOfSurjective hf).symm.toLinearMap,
    fun x => ?_⟩
  have e : (f.quotKerEquivOfSurjective hf).symm (f x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp [e]

theorem genSub_stab (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) :
    ∀ Z, ∀ y ∈ genSub act S, act Z y ∈ genSub act S := fun Z y hy =>
  Submodule.mem_sInf.2 fun _ hN => hN.2 Z y (Submodule.mem_sInf.1 hy _ hN)

theorem subset_gen (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (x : V) : x ∈ genSub act {x} :=
  Submodule.mem_sInf.2 fun _ hN => hN.1 rfl

theorem gen_le (act : Mat p q →ₗ[ℂ] Module.End ℂ V) {x : V} {U : Submodule ℂ V} (hx : x ∈ U)
    (hU : ∀ Z, ∀ y ∈ U, act Z y ∈ U) : genSub act {x} ≤ U :=
  sInf_le ⟨Set.singleton_subset_iff.2 hx, hU⟩

end General

section Constructions

def prodAct (M M' : GKMod p q) : Mat p q →ₗ[ℂ] Module.End ℂ (M.V × M'.V) where
  toFun Z := LinearMap.prodMap (M.act Z) (M'.act Z)
  map_add' X Y := LinearMap.ext fun x => by simp
  map_smul' c X := LinearMap.ext fun x => by simp

theorem prodAct_apply (M M' : GKMod p q) (Z : Mat p q) (x : M.V × M'.V) :
    prodAct M M' Z x = (M.act Z x.1, M'.act Z x.2) := rfl

def prodMod (M M' : GKMod p q) : GKMod p q where
  V := M.V × M'.V
  act := prodAct M M'
  lie X Y := by
    apply LinearMap.ext; rintro ⟨x, x'⟩
    have h1 := LinearMap.congr_fun (M.lie X Y) x
    have h2 := LinearMap.congr_fun (M'.lie X Y) x'
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1 h2
    simp only [LinearMap.sub_apply, Module.End.mul_apply, prodAct_apply, h1, h2, Prod.mk_sub_mk]
  kfin := by
    rintro ⟨x, x'⟩
    obtain ⟨W, hW, hx, hs⟩ := M.kfin x
    obtain ⟨W', hW', hx', hs'⟩ := M'.kfin x'
    haveI := hW; haveI := hW'
    refine ⟨LinearMap.range (LinearMap.prodMap W.subtype W'.subtype), inferInstance,
      ⟨(⟨x, hx⟩, ⟨x', hx'⟩), rfl⟩, ?_⟩
    rintro Z hZ _ ⟨⟨y, y'⟩, rfl⟩
    exact ⟨(⟨M.act Z y, hs Z hZ y y.2⟩, ⟨M'.act Z y', hs' Z hZ y' y'.2⟩), rfl⟩
  wts := by
    rintro ⟨x, x'⟩
    have h1 := map_wts (b := prodAct M M') (LinearMap.inl ℂ M.V M'.V)
      (fun Z v => by simp [prodAct_apply]) (M.wts x)
    have h2 := map_wts (b := prodAct M M') (LinearMap.inr ℂ M.V M'.V)
      (fun Z v => by simp [prodAct_apply]) (M'.wts x')
    have := add_mem h1 h2
    simpa using this

def subAct (M : GKMod p q) (U : Submodule ℂ M.V) (h : ∀ Z, ∀ x ∈ U, M.act Z x ∈ U) :
    Mat p q →ₗ[ℂ] Module.End ℂ U where
  toFun Z := (M.act Z).restrict (h Z)
  map_add' X Y := by ext x; simp [LinearMap.restrict_apply]
  map_smul' c X := by ext x; simp [LinearMap.restrict_apply]

def subMod (M : GKMod p q) (U : Submodule ℂ M.V) (h : ∀ Z, ∀ x ∈ U, M.act Z x ∈ U) : GKMod p q where
  V := U
  act := subAct M U h
  lie X Y := by
    ext x
    have := LinearMap.congr_fun (M.lie X Y) (x : M.V)
    simpa [subAct, LinearMap.restrict_apply] using this
  kfin v := by
    obtain ⟨W, hW, hv, hs⟩ := M.kfin v
    haveI := hW
    refine ⟨W.comap U.subtype, ?_, hv, fun X hX w hw => hs X hX w hw⟩
    exact Module.Finite.of_injective
      (U.subtype.restrict (p := W.comap U.subtype) (q := W) (fun x hx => hx))
      (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun z : W => (z : M.V)) hab)))
  wts v := by
    have h1 := GlobalTheory.BlockReps.decomp (act := M.act) (W := U) (fun Z _ w hw => h Z w hw) v.2 (M.wts v)
    have h2 : (⨆ μ : Ix p q → ℚ, U ⊓ wtSub M.act μ) ≤
        (⨆ μ : Ix p q → ℚ, wtSub (subAct M U h) μ).map U.subtype := by
      refine iSup_le fun μ x hx => ?_
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      refine Submodule.mem_iSup_of_mem μ ?_
      have hx2 := hx.2
      simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker] at hx2 ⊢
      intro a
      apply Subtype.ext
      simpa [subAct, LinearMap.restrict_apply] using hx2 a
    obtain ⟨y, hy, hyv⟩ := h2 h1
    have : y = v := Subtype.ext hyv
    exact this ▸ hy

def quotMod (M : GKMod p q) (N : Submodule ℂ M.V) (hN : ∀ Z, ∀ y ∈ N, M.act Z y ∈ N) : GKMod p q where
  V := M.V ⧸ N
  act :=
    { toFun := fun Z => N.mapQ N (M.act Z) fun y hy => hN Z y hy
      map_add' := fun Y Z => by
        refine Submodule.linearMap_qext _ ?_
        ext v; simp
      map_smul' := fun c Z => by
        refine Submodule.linearMap_qext _ ?_
        ext v; simp }
  lie := fun Y Z => by
    refine Submodule.linearMap_qext _ ?_
    ext v
    have := LinearMap.congr_fun (M.lie Y Z) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, LinearMap.sub_apply, Module.End.mul_apply, this, Submodule.Quotient.mk_sub]
  kfin := fun v => by
    obtain ⟨v, rfl⟩ := N.mkQ_surjective v
    obtain ⟨W, hW, hv, hst⟩ := M.kfin v
    refine ⟨W.map N.mkQ, inferInstance, Submodule.mem_map_of_mem hv, ?_⟩
    rintro Z hZ _ ⟨w, hw, rfl⟩
    exact ⟨M.act Z w, hst Z hZ w hw, rfl⟩
  wts := fun v => by
    obtain ⟨v, rfl⟩ := N.mkQ_surjective v
    exact map_wts (b := _) N.mkQ (fun Z x => rfl) (M.wts v)

end Constructions

section Max

def maxSub (X : GKMod p q) (x0 : X.V) : Submodule ℂ X.V :=
  sSup {U | (∀ Z, ∀ y ∈ U, X.act Z y ∈ U) ∧ x0 ∉ U}

theorem zero_of_line {X : GKMod p q} {x0 : X.V} {Λ : Ix p q → ℚ}
    (hone : ∀ w ∈ hwSub X.act Λ, ∃ c : ℂ, w = c • x0) {U : Submodule ℂ X.V} (hU : x0 ∉ U)
    {w : X.V} (hw : w ∈ hwSub X.act Λ) (hwU : w ∈ U) : w = 0 := by
  obtain ⟨c, rfl⟩ := hone w hw
  by_cases hc : c = 0
  · simp [hc]
  · exfalso; apply hU
    have := U.smul_mem c⁻¹ hwU
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem stab_sup {X : GKMod p q} {A B : Submodule ℂ X.V} (hA : ∀ Z, ∀ y ∈ A, X.act Z y ∈ A)
    (hB : ∀ Z, ∀ y ∈ B, X.act Z y ∈ B) : ∀ Z, ∀ y ∈ A ⊔ B, X.act Z y ∈ A ⊔ B := by
  intro Z y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add]; exact Submodule.add_mem_sup (hA Z a ha) (hB Z b hb)

theorem notMem_sup {X : GKMod p q} {x0 : X.V} {Λ : Ix p q → ℚ} (hx0 : IsHW X.act Λ x0)
    (hone : ∀ w ∈ hwSub X.act Λ, ∃ c : ℂ, w = c • x0) {A B : Submodule ℂ X.V}
    (hA : ∀ Z, ∀ y ∈ A, X.act Z y ∈ A) (hB : ∀ Z, ∀ y ∈ B, X.act Z y ∈ B)
    (hxA : x0 ∉ A) (hxB : x0 ∉ B) : x0 ∉ A ⊔ B := by
  intro hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨W, hW, hzW, hWs⟩ := X.kfin z
  haveI := hW
  haveI : FiniteDimensional ℂ ↥(W ⊓ B) := Submodule.finiteDimensional_of_le inf_le_left
  have sB : KStable X.act B := fun Z _ w hw => hB Z w hw
  have sA : KStable X.act A := fun Z _ w hw => hA Z w hw
  have hm : x0 ∈ A ⊔ (W ⊓ B) := by rw [← hyz]; exact Submodule.add_mem_sup hy ⟨hzW, hz⟩
  obtain ⟨y', hy', z', hz', h1, h2, h3⟩ := hw_sup (a := X.act) (fun Y Z _ _ => X.lie Y Z) X.wts sA
    (GlobalTheory.BlockReps.stable_inf hWs sB) hm hx0.2
  have e1 := zero_of_line hone hxA h1 hy'
  have e2 := zero_of_line hone hxB h2 hz'.2
  apply hx0.1
  rw [← h3, e1, e2, add_zero]

theorem max_spec {X : GKMod p q} {x0 : X.V} {Λ : Ix p q → ℚ} (hx0 : IsHW X.act Λ x0)
    (hone : ∀ w ∈ hwSub X.act Λ, ∃ c : ℂ, w = c • x0) :
    (∀ Z, ∀ y ∈ maxSub X x0, X.act Z y ∈ maxSub X x0) ∧ x0 ∉ maxSub X x0 := by
  have hne : ({U | (∀ Z, ∀ y ∈ U, X.act Z y ∈ U) ∧ x0 ∉ U} : Set (Submodule ℂ X.V)).Nonempty :=
    ⟨⊥, fun Z y hy => by rw [Submodule.mem_bot] at hy ⊢; rw [hy, map_zero],
      fun h => hx0.1 ((Submodule.mem_bot ℂ).1 h)⟩
  have hdir : DirectedOn (· ≤ ·)
      ({U | (∀ Z, ∀ y ∈ U, X.act Z y ∈ U) ∧ x0 ∉ U} : Set (Submodule ℂ X.V)) := by
    rintro A ⟨hA, hxA⟩ B ⟨hB, hxB⟩
    exact ⟨A ⊔ B, ⟨stab_sup hA hB, notMem_sup hx0 hone hA hB hxA hxB⟩, le_sup_left, le_sup_right⟩
  refine ⟨fun Z y hy => ?_, fun h => ?_⟩
  · obtain ⟨U, hU, hyU⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hy
    exact le_sSup hU (hU.1 Z y hyU)
  · obtain ⟨U, hU, hyU⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 h
    exact hU.2 hyU

theorem le_max_or_top {X : GKMod p q} {x0 : X.V} (hgen : genSub X.act {x0} = ⊤)
    {U : Submodule ℂ X.V} (hU : ∀ Z, ∀ y ∈ U, X.act Z y ∈ U) : U ≤ maxSub X x0 ∨ U = ⊤ := by
  by_cases h : x0 ∈ U
  · right; rw [eq_top_iff, ← hgen]
    exact gen_le _ h hU
  · left; exact le_sSup ⟨hU, h⟩

def qmap (X : GKMod p q) (U : Submodule ℂ X.V) (hU : ∀ Z, ∀ y ∈ U, X.act Z y ∈ U) :
    X.V →ₗ[ℂ] (quotMod X U hU).V := U.mkQ

theorem qmap_surj (X : GKMod p q) (U : Submodule ℂ X.V) (hU : ∀ Z, ∀ y ∈ U, X.act Z y ∈ U) :
    Function.Surjective (qmap X U hU) := U.mkQ_surjective

theorem qmap_eq_zero {X : GKMod p q} {U : Submodule ℂ X.V} {hU : ∀ Z, ∀ y ∈ U, X.act Z y ∈ U}
    {x : X.V} : qmap X U hU x = 0 ↔ x ∈ U := Submodule.Quotient.mk_eq_zero U

theorem qmap_act (X : GKMod p q) (U : Submodule ℂ X.V) (hU : ∀ Z, ∀ y ∈ U, X.act Z y ∈ U)
    (Z : Mat p q) (x : X.V) : qmap X U hU (X.act Z x) = (quotMod X U hU).act Z (qmap X U hU x) := rfl

theorem quot_of_ker {X Y : GKMod p q} (U : Submodule ℂ X.V) (hU : ∀ Z, ∀ y ∈ U, X.act Z y ∈ U)
    (f : X.V →ₗ[ℂ] Y.V) (hf : Function.Surjective f) (hfe : ∀ Z x, f (X.act Z x) = Y.act Z (f x))
    (hker : LinearMap.ker f ≤ U) :
    ∃ π : Y.V →ₗ[ℂ] (quotMod X U hU).V, GlobalTheory.RealLift.IsQuot Y (quotMod X U hU) π := by
  obtain ⟨π, hπ⟩ := exists_factor f hf (qmap X U hU)
    (fun x hx => qmap_eq_zero.2 (hker hx))
  refine ⟨π, fun n => ?_, fun Z y => ?_⟩
  · obtain ⟨x, rfl⟩ := qmap_surj X U hU n
    exact ⟨f x, hπ x⟩
  · obtain ⟨x, rfl⟩ := hf y
    rw [← hfe, hπ, hπ, qmap_act]

end Max

section Main

def incl (X : GKMod p q) (U : Submodule ℂ X.V) (hU : ∀ Z, ∀ y ∈ U, X.act Z y ∈ U) :
    (subMod X U hU).V →ₗ[ℂ] X.V := U.subtype

theorem incl_inj (X : GKMod p q) (U : Submodule ℂ X.V) (hU : ∀ Z, ∀ y ∈ U, X.act Z y ∈ U) :
    Function.Injective (incl X U hU) := U.injective_subtype

theorem incl_act (X : GKMod p q) (U : Submodule ℂ X.V) (hU : ∀ Z, ∀ y ∈ U, X.act Z y ∈ U)
    (Z : Mat p q) (x : (subMod X U hU).V) : incl X U hU ((subMod X U hU).act Z x) = X.act Z (incl X U hU x) :=
  rfl

theorem incl_range (X : GKMod p q) (U : Submodule ℂ X.V) (hU : ∀ Z, ∀ y ∈ U, X.act Z y ∈ U)
    {y : X.V} (hy : y ∈ U) : ∃ x, incl X U hU x = y := ⟨⟨y, hy⟩, rfl⟩

def fstP (M M' : GKMod p q) : (prodMod M M').V →ₗ[ℂ] M.V := LinearMap.fst ℂ M.V M'.V

def sndP (M M' : GKMod p q) : (prodMod M M').V →ₗ[ℂ] M'.V := LinearMap.snd ℂ M.V M'.V

def pairP (M M' : GKMod p q) (x : M.V) (x' : M'.V) : (prodMod M M').V := (x, x')

theorem snd_act₂ (M M' : GKMod p q) (Z : Mat p q) (x : (prodMod M M').V) :
    sndP M M' ((prodMod M M').act Z x) = M'.act Z (sndP M M' x) := rfl

theorem eq_zero_of_fst_snd (M M' : GKMod p q) {x : (prodMod M M').V} (h1 : fstP M M' x = 0)
    (h2 : sndP M M' x = 0) : x = 0 := Prod.ext h1 h2

theorem pairP_mem_highestWeight (M M' : GKMod p q) {Λ : Ix p q → ℚ} {v : M.V} {v' : M'.V}
    (hv : v ∈ hwSub M.act Λ) (hv' : v' ∈ hwSub M'.act Λ) :
    pairP M M' v v' ∈ hwSub (prodMod M M').act Λ := by
  rw [mem_hwSub'] at hv hv' ⊢
  refine ⟨fun a => ?_, fun a b h => ?_⟩
  · show ((M.act (Eab a a) v - ((Λ a : ℚ) : ℂ) • v, M'.act (Eab a a) v' - ((Λ a : ℚ) : ℂ) • v') :
      M.V × M'.V) = 0
    rw [hv.1 a, hv'.1 a]; rfl
  · show ((M.act (Eab a b) v, M'.act (Eab a b) v') : M.V × M'.V) = 0
    rw [hv.2 a b h, hv'.2 a b h]; rfl

theorem snd_pair₂ (M M' : GKMod p q) (x : M.V) (x' : M'.V) : sndP M M' (pairP M M' x x') = x' := rfl

theorem surj_of_gen {X Y : GKMod p q} (f : X.V →ₗ[ℂ] Y.V) (hfe : ∀ Z x, f (X.act Z x) = Y.act Z (f x))
    {x0 : X.V} (hgen : genSub Y.act {f x0} = ⊤) : Function.Surjective f := by
  have : LinearMap.range f = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact gen_le _ (LinearMap.mem_range.2 ⟨x0, rfl⟩)
      (by rintro Z _ ⟨x, rfl⟩; exact ⟨X.act Z x, hfe Z x⟩)
  exact LinearMap.range_eq_top.1 this

theorem common_quotient : GlobalTheory.RealLift.MultOne → ∀ (R S : ℕ) (M M' : Formalism.BasicNotions.TH.GKMod R S)
    (Λ : Formalism.BasicNotions.TH.Ix R S → ℚ), GlobalTheory.RealLift.GenBy M Λ → GlobalTheory.RealLift.GenBy M' Λ →
    GlobalTheory.RealLift.Steep M Λ → GlobalTheory.RealLift.Steep M' Λ →
    ∃ (N : Formalism.BasicNotions.TH.GKMod R S) (π : M.V →ₗ[ℂ] N.V) (π' : M'.V →ₗ[ℂ] N.V),
      GlobalTheory.RealLift.IsQuot M N π ∧ GlobalTheory.RealLift.IsQuot M' N π' ∧ Formalism.MainNotions.SchurIrreducible.IrrGK N ∧
        GlobalTheory.RealLift.ScalarEnd N := by
  intro hMO R S M M' Λ ⟨v, hv, hvg⟩ ⟨v', hv', hvg'⟩ hM hM'
  let P := prodMod M M'
  let D : Submodule ℂ P.V := genSub P.act {pairP M M' v v'}
  have hDs : ∀ Z, ∀ y ∈ D, P.act Z y ∈ D := genSub_stab P.act _
  let X := subMod P D hDs
  let i := incl P D hDs
  obtain ⟨d0, hd0i⟩ := incl_range P D hDs (subset_gen P.act (pairP M M' v v'))
  let p1 : X.V →ₗ[ℂ] M.V := fstP M M' ∘ₗ i
  let p2 : X.V →ₗ[ℂ] M'.V := sndP M M' ∘ₗ i
  have hp1 : ∀ Z x, p1 (X.act Z x) = M.act Z (p1 x) := fun _ _ => rfl
  have hp2 : ∀ Z x, p2 (X.act Z x) = M'.act Z (p2 x) := fun _ _ => rfl
  have hp1d : p1 d0 = v := by
    show fstP M M' (i d0) = v; rw [hd0i]; rfl
  have hp2d : p2 d0 = v' := by
    show sndP M M' (i d0) = v'; rw [hd0i]; rfl
  have hL : IsKLieAct X.act := fun Y Z _ _ => X.lie Y Z

  have hd0 : IsHW X.act Λ d0 := by
    refine ⟨fun h => hv.1 ?_, hw_of_inj i (incl_act P D hDs) (incl_inj P D hDs) ?_⟩
    · rw [← hp1d, h, map_zero]
    · rw [hd0i]; exact pairP_mem_highestWeight M M' hv.2 hv'.2
  have hgen : genSub X.act {d0} = ⊤ := by
    rw [eq_top_iff]
    intro d _
    have hle : D ≤ (genSub X.act {d0}).map i := by
      refine gen_le _ ⟨d0, subset_gen _ _, hd0i⟩ ?_
      intro Z y hy
      obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.1 hy
      exact Submodule.mem_map.2 ⟨X.act Z s, genSub_stab _ _ Z s hs, incl_act P D hDs Z s⟩
    obtain ⟨s, hs, hsd⟩ := Submodule.mem_map.1 (hle d.2)
    have : s = d := incl_inj P D hDs hsd
    rwa [this] at hs
  have hst : GlobalTheory.RealLift.Steep X Λ := by
    intro a b hab w hw
    by_cases h1 : p1 w = 0
    · have h2 : p2 w ≠ 0 := by
        intro h2; apply hw.1
        exact incl_inj P D hDs (by rw [map_zero]; exact eq_zero_of_fst_snd M M' h1 h2)
      exact hM' a b hab _ ⟨h2, map_hw p2 hp2 hw.2⟩
    · exact hM a b hab _ ⟨h1, map_hw p1 hp1 hw.2⟩
  have hone := hMO R S X Λ d0 hd0 hgen hst
  obtain ⟨hmaxs, hmax0⟩ := max_spec hd0 hone
  let N := quotMod X (maxSub X d0) hmaxs
  let mk := qmap X (maxSub X d0) hmaxs
  have hmk : ∀ Z x, mk (X.act Z x) = N.act Z (mk x) := qmap_act X (maxSub X d0) hmaxs

  have hker : ∀ {Y : GKMod R S} (f : X.V →ₗ[ℂ] Y.V), (∀ Z x, f (X.act Z x) = Y.act Z (f x)) →
      f d0 ≠ 0 → LinearMap.ker f ≤ maxSub X d0 := by
    intro Y f hf hf0
    rcases le_max_or_top hgen (U := LinearMap.ker f) (fun Z y hy => by
        rw [LinearMap.mem_ker] at hy ⊢; rw [hf, hy, map_zero]) with h | h
    · exact h
    · exfalso
      have : d0 ∈ LinearMap.ker f := by rw [h]; exact Submodule.mem_top
      exact hf0 this
  obtain ⟨π, hπ⟩ := quot_of_ker (maxSub X d0) hmaxs p1
    (surj_of_gen p1 hp1 (x0 := d0) (by rw [hp1d]; exact hvg)) hp1
    (hker p1 hp1 (by rw [hp1d]; exact hv.1))
  obtain ⟨π', hπ'⟩ := quot_of_ker (maxSub X d0) hmaxs p2
    (surj_of_gen p2 hp2 (x0 := d0) (by rw [hp2d]; exact hvg')) hp2
    (hker p2 hp2 (by rw [hp2d]; exact hv'.1))
  have hn0 : mk d0 ≠ 0 := fun h => hmax0 (qmap_eq_zero.1 h)
  refine ⟨N, π, π', hπ, hπ', ⟨nontrivial_of_ne (mk d0) 0 hn0, fun L hL' => ?_⟩, fun T hT => ?_⟩
  · rcases le_max_or_top hgen (U := L.comap mk) (fun Z y hy => by
        rw [Submodule.mem_comap] at hy ⊢; rw [hmk]; exact hL' Z _ hy) with h | h
    · left; rw [eq_bot_iff]; intro n hn
      obtain ⟨d, rfl⟩ := qmap_surj X (maxSub X d0) hmaxs n
      rw [Submodule.mem_bot]
      exact qmap_eq_zero.2 (h hn)
    · right; rw [eq_top_iff]; intro n _
      obtain ⟨d, rfl⟩ := qmap_surj X (maxSub X d0) hmaxs n
      have : d ∈ L.comap mk := by rw [h]; exact Submodule.mem_top
      exact this
  · have hTe : ∀ Z y, T (N.act Z y) = N.act Z (T y) := fun Z y => LinearMap.congr_fun (hT Z) y
    have hn0w : mk d0 ∈ hwSub N.act Λ := map_hw mk hmk hd0.2
    have hTn : T (mk d0) ∈ hwSub N.act Λ := map_hw T hTe hn0w
    obtain ⟨d1, hd1⟩ := qmap_surj X (maxSub X d0) hmaxs (T (mk d0))
    obtain ⟨W, hW, hd1W, hWs⟩ := X.kfin d1
    haveI := hW
    obtain ⟨u, hu, hgu⟩ := hw_lift hL X.wts mk hmk hWs hd1W (by
      show mk d1 ∈ hwSub N.act Λ
      rw [show mk d1 = T (mk d0) from hd1]; exact hTn)
    obtain ⟨c, rfl⟩ := hone u hu
    refine ⟨c, ?_⟩
    have hTc : T (mk d0) = c • mk d0 := by
      rw [← show mk d1 = T (mk d0) from hd1, ← hgu, map_smul]
    have hK : genSub X.act {d0} ≤ (LinearMap.ker (T - c • LinearMap.id)).comap mk := by
      refine gen_le _ ?_ ?_
      · rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
          LinearMap.id_apply, hTc, sub_self]
      · intro Z y hy
        rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
          LinearMap.id_apply] at hy ⊢
        rw [hmk, hTe, ← map_smul, ← map_sub, hy, map_zero]
    apply LinearMap.ext; intro n
    obtain ⟨d, rfl⟩ := qmap_surj X (maxSub X d0) hmaxs n
    have := hK (by rw [hgen]; exact Submodule.mem_top : d ∈ genSub X.act {d0})
    rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this

end Main

end GlobalTheory.CommonQuot
