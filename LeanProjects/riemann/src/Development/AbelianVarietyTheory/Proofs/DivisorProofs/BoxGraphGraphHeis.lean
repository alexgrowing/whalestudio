import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.BigDat.GraphHeis

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

variable {D : D7}

theorem isHalf_nsmul' {m n : ℕ} {ε : AE D} {a : Mx D m n} (ha : IsHalf ε a) (k : ℕ) : IsHalf ε (k • a) :=
  fun i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, ha i j]

theorem isHalf_of_add' {m n : ℕ} {ε : AE D} {a b : Mx D m n} (h : IsHalf ε (a + b)) (hb : IsHalf ε b) : IsHalf ε a :=
  fun i j => by
    have h1 := h i j
    rw [Matrix.add_apply, mul_add, hb i j] at h1
    exact add_right_cancel h1

theorem sb_trans {m n : ℕ} {ε : AE D} {Λ : AddSubgroup (Mx D m n)} {φ : Mx D m n → ℂ} (h : IsSBHalf ε Λ φ)
    {x : Mx D m n} (hx : IsHalf ε x) {k₀ : ℕ} (hk₀ : 0 < k₀) (hkx : k₀ • x ∈ Λ) :
    IsSBHalf ε Λ (fun t => φ (t + x)) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  refine ⟨fun t ht => isHalf_of_add' (h1 _ ht) hx, k * k₀, Nat.mul_pos hk hk₀, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · show φ (t + (k * k₀) • u + x) = φ (t + x)
    rw [show t + (k * k₀) • u + x = (t + x) + k • (k₀ • u) by rw [mul_smul]; abel]
    exact h2 _ (nsmul_mem hu k₀) (isHalf_nsmul' hu' k₀) _
  · have e : (k * k₀) • t = k₀ • (k • (t + x)) - k • (k₀ • x) := by
      rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, mul_comm k₀ k]; abel
    rw [e]
    exact sub_mem (nsmul_mem (h3 _ ht) k₀) (nsmul_mem hkx k)

theorem sb_modul {m n : ℕ} {ε : AE D} {Λ : AddSubgroup (Mx D m n)} {φ : Mx D m n → ℂ} (h : IsSBHalf ε Λ φ)
    (χ : Mx D m n → ℂ) (hχ : ∀ a b, χ (a + b) = χ a * χ b) {k₀ : ℕ} (hk₀ : 0 < k₀)
    (h1χ : ∀ u ∈ Λ, IsHalf ε u → χ (k₀ • u) = 1) : IsSBHalf ε Λ (fun t => χ t * φ t) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  refine ⟨fun t ht => h1 t (right_ne_zero_of_mul ht), k₀ * k, Nat.mul_pos hk₀ hk, fun u hu hu' t => ?_,
    fun t ht => ?_⟩
  · show χ (t + (k₀ * k) • u) * φ (t + (k₀ * k) • u) = χ t * φ t
    rw [hχ, mul_smul, h1χ _ (nsmul_mem hu k) (isHalf_nsmul' hu' k), mul_one, smul_comm k₀ k u,
      h2 _ (nsmul_mem hu k₀) (isHalf_nsmul' hu' k₀)]
  · rw [mul_smul]
    exact nsmul_mem (h3 t (right_ne_zero_of_mul ht)) k₀

theorem symplO_add_left' (S T : HSp D) (x x' y : WO S T) : symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  simp only [symplO, hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib, LinearMap.map_add]

theorem symplO_add_right' (S T : HSp D) (x y y' : WO S T) : symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO, hO, Matrix.add_apply, RingHom.map_add, map_add (cA D), mul_add, add_mul, Finset.sum_add_distrib,
    LinearMap.map_add]

theorem symplO_nsmul' (S T : HSp D) (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = symplO S T x (k • y) := by
  have h1 := map_nsmul (AddMonoidHom.mk' (fun x => symplO S T x y) fun a b => symplO_add_left' S T a b y) k x
  have h2 := map_nsmul (AddMonoidHom.mk' (fun y => symplO S T x y) fun a b => symplO_add_right' S T x a b) k y
  exact h1.trans h2.symm

theorem map_infPart_of_half {S T : HSp D} {a : AE D} (ha : infPart D a = 0) {u : WO S T} (hu : IsHalf a u) :
    u.map (infPart D) = 0 := by
  ext i j
  show infPart D (u i j) = 0
  rw [← hu i j, map_mul, ha, zero_mul]

theorem sb_trans_latO {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : Submodule.IsLattice D.host.E ΛS)
    (hT : Submodule.IsLattice D.host.E ΛT) {ε : AE D} (hinf : infPart D ε = 0) {φ : WO S T → ℂ}
    (h : IsSBHalf ε (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) φ)
    {x : WO S T} (hx : IsHalf ε x) :
    IsSBHalf ε (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (fun t => φ (t + x)) := by
  obtain ⟨k, hk, hkx⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_latO hS hT x (map_infPart_of_half hinf hx)
  exact sb_trans h hx hk hkx

theorem sb_modul_latO {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {ε : AE D} (hinf : infPart D (cA D ε) = 0) {φ : WO S T → ℂ}
    (h : IsSBHalf ε (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) φ)
    {y : WO S T} (hy : IsHalf (cA D ε) y) :
    IsSBHalf ε (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (fun t => ψ (symplO S T t y) * φ t) := by
  obtain ⟨k, hk, hky⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_latO hS.1 hT.1 y (map_infPart_of_half hinf hy)
  refine sb_modul h (fun t => ψ (symplO S T t y)) (fun a b => ?_) hk (fun u hu _ => ?_)
  · show ψ (symplO S T (a + b) y) = ψ (symplO S T a y) * ψ (symplO S T b y)
    rw [symplO_add_left', AddChar.map_add_eq_mul]
  · show ψ (symplO S T (k • u) y) = 1
    rw [symplO_nsmul']
    exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hu hky

end GlobalTheory.BigDat.GraphHeis

namespace GlobalTheory.BigDat

open GlobalTheory.BigDat.GraphHeis

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

def graphMap (e : Num G i j) (T₁ : (HomV G i j → ℂ) →ₗ[ℂ] (HomV G i j → ℂ))
    (T₂ : (HomW G i j → ℂ) →ₗ[ℂ] (HomW G i j → ℂ)) : (Pt G i j → ℂ) →ₗ[ℂ] (Pt G i j → ℂ) where
  toFun g u := T₁ (fun x => T₂ (fun y => g (ofMaps e (x, y))) (mapW e u)) (mapV e u)
  map_add' g g' := funext fun u => by
    have h : (fun x => T₂ (fun y => (g + g') (ofMaps e (x, y))) (mapW e u)) =
        (fun x => T₂ (fun y => g (ofMaps e (x, y))) (mapW e u)) + fun x => T₂ (fun y => g' (ofMaps e (x, y))) (mapW e u) :=
      funext fun x => by
        show T₂ ((fun y => g (ofMaps e (x, y))) + fun y => g' (ofMaps e (x, y))) (mapW e u) = _
        rw [map_add]; rfl
    show T₁ (fun x => T₂ (fun y => (g + g') (ofMaps e (x, y))) (mapW e u)) (mapV e u) = _
    rw [h, map_add]; rfl
  map_smul' c g := funext fun u => by
    have h : (fun x => T₂ (fun y => (c • g) (ofMaps e (x, y))) (mapW e u)) =
        c • fun x => T₂ (fun y => g (ofMaps e (x, y))) (mapW e u) :=
      funext fun x => by
        show T₂ (c • fun y => g (ofMaps e (x, y))) (mapW e u) = _
        rw [map_smul]; rfl
    show T₁ (fun x => T₂ (fun y => (c • g) (ofMaps e (x, y))) (mapW e u)) (mapV e u) = _
    rw [h, map_smul]; rfl

theorem graphMap_box (e : Num G i j) (T₁ : (HomV G i j → ℂ) →ₗ[ℂ] (HomV G i j → ℂ))
    (T₂ : (HomW G i j → ℂ) →ₗ[ℂ] (HomW G i j → ℂ)) (φ₁ : HomV G i j → ℂ) (φ₂ : HomW G i j → ℂ) :
    graphMap e T₁ T₂ (box e φ₁ φ₂) = box e (T₁ φ₁) (T₂ φ₂) := funext fun u => by
  have e2 : ∀ x, (fun y => box e φ₁ φ₂ (ofMaps e (x, y))) = φ₁ x • φ₂ := fun x => funext fun y => by
    show φ₁ (mapV e (ofMaps e (x, y))) * φ₂ (mapW e (ofMaps e (x, y))) = φ₁ x * φ₂ y
    rw [mapV_ofMaps, mapW_ofMaps]
  have e1 : (fun x => T₂ (fun y => box e φ₁ φ₂ (ofMaps e (x, y))) (mapW e u)) = T₂ φ₂ (mapW e u) • φ₁ :=
    funext fun x => by
      rw [e2, map_smul]
      show φ₁ x * T₂ φ₂ (mapW e u) = T₂ φ₂ (mapW e u) * φ₁ x
      exact mul_comm _ _
  show T₁ (fun x => T₂ (fun y => box e φ₁ φ₂ (ofMaps e (x, y))) (mapW e u)) (mapV e u) = T₁ φ₁ (mapV e u) * T₂ φ₂ (mapW e u)
  rw [e1, map_smul]
  show T₂ φ₂ (mapW e u) * T₁ φ₁ (mapV e u) = _
  exact mul_comm _ _

def transPair (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (x : Pt G i j) :
    ((Pt G i j → ℂ) × (Pt G i j → ℂ)) →ₗ[ℂ] ((Pt G i j → ℂ) × (Pt G i j → ℂ)) where
  toFun p := (fun u => p.1 (u + x), heisPt Γ ψ x p.2)
  map_add' p q := Prod.ext rfl (funext fun u => mul_add _ _ _)
  map_smul' c p := Prod.ext rfl (funext fun u => mul_left_comm _ _ _)

def modulPair (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (y : Pt G i j) :
    ((Pt G i j → ℂ) × (Pt G i j → ℂ)) →ₗ[ℂ] ((Pt G i j → ℂ) × (Pt G i j → ℂ)) where
  toFun p := (fun u => ψ (sympPt Γ u y) * p.1 u, heisPt Γ ψ y p.2)
  map_add' p q := Prod.ext (funext fun u => mul_add _ _ _) (funext fun u => mul_add _ _ _)
  map_smul' c p := Prod.ext (funext fun u => mul_left_comm _ _ _) (funext fun u => mul_left_comm _ _ _)

end GlobalTheory.BigDat

set_option maxHeartbeats 1600000 in
open GlobalTheory.BigDat.GraphHeis in

theorem GlobalTheory.BigDat.boxGraph_graph_heis : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e → ∀ (ε : AE D) (P : Finset (Pl D.host.E)), IsIdemSum ε P →
    ∀ (f₁ : HomV G i j → ℂ) (f₂ : HomW G i j → ℂ) (T₁ : (HomV G i j → ℂ) →ₗ[ℂ] (HomV G i j → ℂ))
      (T₂ : (HomW G i j → ℂ) →ₗ[ℂ] (HomW G i j → ℂ)),
    IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) ε (latV G i j) 1 f₁ T₁ →
    IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) ε (latW G i j) 1 f₂ T₂ →
    (∀ f, (0, f) ∈ boxGraph e ε T₁ T₂ → f = 0) ∧
    (∀ x ∈ mixHalf e ε, ∀ p ∈ boxGraph e ε T₁ T₂, (fun u => p.1 (u + x), heisPt Γ W.ψ x p.2) ∈ boxGraph e ε T₁ T₂) ∧
    ∀ y ∈ mixHalf e (cA D ε), ∀ p ∈ boxGraph e ε T₁ T₂,
      (fun u => W.ψ (sympPt Γ u y) * p.1 u, heisPt Γ W.ψ y p.2) ∈ boxGraph e ε T₁ T₂ := by
  intro D T L sc G μ₀ hL W i j e Γ hW hWW ε P hε f₁ f₂ T₁ T₂ h₁ h₂
  have hinf : infPart D ε = 0 := GlobalTheory.PlaceVec.idemSum_infPart hε
  have hinf' : infPart D (cA D ε) = 0 := GlobalTheory.PlaceVec.infPart_cA hinf
  have sdW : IsSelfDualC (spW G i j) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).sd
  have sdV : IsSelfDualC (spV G i j) (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have sdV₁ : IsSelfDualC (spV₁ G i j) (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  have sdW' : IsSelfDualC (negSp (spW G i j)) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) := isSelfDualC_neg sdW
  refine ⟨fun f hf => ?_, fun x hx p hp => ?_, fun y hy p hp => ?_⟩
  · have key : boxGraph e ε T₁ T₂ ≤ LinearMap.ker (LinearMap.snd ℂ _ _ - graphMap e T₁ T₂ ∘ₗ LinearMap.fst ℂ _ _) := by
      refine Submodule.span_le.2 fun p hp => ?_
      obtain ⟨φ₁, φ₂, -, -, rfl⟩ := hp
      show box e (T₁ φ₁) (T₂ φ₂) - graphMap e T₁ T₂ (box e φ₁ φ₂) = 0
      rw [graphMap_box, sub_self]
    have h0 := key hf
    rw [LinearMap.mem_ker] at h0
    have h1 : f - graphMap e T₁ T₂ 0 = 0 := h0
    rwa [map_zero, sub_zero] at h1
  · have key : boxGraph e ε T₁ T₂ ≤ (boxGraph e ε T₁ T₂).comap (transPair Γ W.ψ x) := by
      refine Submodule.span_le.2 fun p hp => ?_
      obtain ⟨φ₁, φ₂, hφ₁, hφ₂, rfl⟩ := hp
      have hx₁ : IsHalf ε (mapV e x) := hx.1
      have hx₂ : IsHalf ε (mapW e x) := hx.2
      have s₁ : IsSBHalf ε (latV G i j) (fun t => φ₁ (t + mapV e x)) :=
        sb_trans_latO (S := negSp (spW G i j)) (T := spV G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)))
          (ΛT := G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) sdW'.1 sdV.1 hinf hφ₁ hx₁
      have s₂ : IsSBHalf ε (latW G i j) (fun t => φ₂ (t + mapW e x)) :=
        sb_trans_latO (S := spV₁ G i j) (T := spW G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) (j : ℕ)))
          (ΛT := G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) sdV₁.1 sdW.1 hinf hφ₂ hx₂
      show (fun u => box e φ₁ φ₂ (u + x), heisPt Γ W.ψ x (box e (T₁ φ₁) (T₂ φ₂))) ∈ boxGraph e ε T₁ T₂
      rw [heisPt_box e Γ hW hWW]
      refine Submodule.subset_span ⟨_, _, s₁, s₂, ?_⟩
      rw [h₁.trans φ₁ hφ₁ _ hx₁, h₂.trans φ₂ hφ₂ _ hx₂]
      refine Prod.ext (funext fun u => ?_) rfl
      show φ₁ (mapV e (u + x)) * φ₂ (mapW e (u + x)) = φ₁ (mapV e u + mapV e x) * φ₂ (mapW e u + mapW e x)
      rw [mapV_add, mapW_add]
    exact key hp
  · have key : boxGraph e ε T₁ T₂ ≤ (boxGraph e ε T₁ T₂).comap (modulPair Γ W.ψ y) := by
      refine Submodule.span_le.2 fun p hp => ?_
      obtain ⟨φ₁, φ₂, hφ₁, hφ₂, rfl⟩ := hp
      have hy₁ : IsHalf (cA D ε) (mapV e y) := hy.1
      have hy₂ : IsHalf (cA D ε) (mapW e y) := hy.2
      have s₁ : IsSBHalf ε (latV G i j) (fun t => W.ψ (symplO _ _ t (mapV e y)) * φ₁ t) :=
        sb_modul_latO (S := negSp (spW G i j)) (T := spV G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)))
          (ΛT := G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) W.ψ_std sdW' sdV hinf' hφ₁ hy₁
      have s₂ : IsSBHalf ε (latW G i j) (fun t => W.ψ (symplO _ _ t (mapW e y)) * φ₂ t) :=
        sb_modul_latO (S := spV₁ G i j) (T := spW G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) (j : ℕ)))
          (ΛT := G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) W.ψ_std sdV₁ sdW hinf' hφ₂ hy₂
      show (fun u => W.ψ (sympPt Γ u y) * box e φ₁ φ₂ u, heisPt Γ W.ψ y (box e (T₁ φ₁) (T₂ φ₂))) ∈ boxGraph e ε T₁ T₂
      rw [heisPt_box e Γ hW hWW]
      refine Submodule.subset_span ⟨_, _, s₁, s₂, ?_⟩
      rw [h₁.modul φ₁ hφ₁ _ hy₁, h₂.modul φ₂ hφ₂ _ hy₂]
      refine Prod.ext (funext fun u => ?_) rfl
      show W.ψ (sympPt Γ u y) * (φ₁ (mapV e u) * φ₂ (mapW e u)) =
        (W.ψ (symplO _ _ (mapV e u) (mapV e y)) * φ₁ (mapV e u)) * (W.ψ (symplO _ _ (mapW e u) (mapW e y)) * φ₂ (mapW e u))
      rw [symp_eq e Γ hW hWW, AddChar.map_add_eq_mul]
      ring
    exact key hp

end
