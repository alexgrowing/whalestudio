import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeC
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open MvPolynomial Module ReciprocityTheory.AnForm.R

theorem gbap_grad_rename {J : Type} [Fintype J] {n : ℕ} (e : J ≃ Fin n) (z₀ : J → ℂ)
    (f : MvPolynomial J ℤ) (j : Fin n) :
    grad (fun j => z₀ (e.symm j)) (map (Int.castRingHom ℂ) (rename e f)) j =
      eval z₀ (pderiv (e.symm j) (map (Int.castRingHom ℂ) f)) := by
  unfold grad
  have h := pderiv_rename (R := ℂ) e.injective (e.symm j) (map (Int.castRingHom ℂ) f)
  rw [Equiv.apply_symm_apply] at h
  have hc : (fun j => z₀ (e.symm j)) ∘ e = z₀ := by
    funext i
    simp
  rw [map_rename, h, eval_rename, hc]

theorem gbap_indep_grads {J : Type} [Fintype J] {D c : ℕ} (e : J ≃ Fin (D + 1 + c))
    (P : Ideal (MvPolynomial J ℤ)) (z₀ : J → ℂ) (T : Submodule ℂ (J → ℂ))
    (hT : ∀ w, w ∈ T ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsConeTangent (Int.castRingHom ℂ) P z₀ w)
    (hTd : finrank ℂ T = D + 1) :
    ∃ f : Fin c → MvPolynomial J ℤ, (∀ i, f i ∈ P) ∧
      LinearIndependent ℂ (fun i => grad (fun j => z₀ (e.symm j))
        (map (Int.castRingHom ℂ) (rename e (f i)))) := by
  classical
  let g : MvPolynomial J ℤ → (J → ℂ) := fun f i => eval z₀ (pderiv i (map (Int.castRingHom ℂ) f))
  obtain ⟨s, hsS, hspan, hsli⟩ := exists_linearIndependent ℂ (g '' (P : Set (MvPolynomial J ℤ)))
  have hfin : Finite s := hsli.finite
  haveI : Fintype s := Fintype.ofFinite s
  let ℓ : (J → ℂ) → (J → ℂ) →ₗ[ℂ] ℂ := fun w =>
    { toFun := fun v => ∑ i, v i * w i
      map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r a => by simp [Finset.mul_sum, mul_assoc] }
  let A : Matrix s J ℂ := Matrix.of fun v i => (v : J → ℂ) i
  have hAli : LinearIndependent ℂ A.row := hsli
  have hker : ∀ w, w ∈ LinearMap.ker A.mulVecLin ↔ w ∈ T := by
    intro w
    rw [LinearMap.mem_ker, hT]
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.IsConeTangent]
    constructor
    · intro hw f hf
      have hle : Submodule.span ℂ (s : Set (J → ℂ)) ≤ LinearMap.ker (ℓ w) := by
        rw [Submodule.span_le]
        intro v hv
        have := congrFun hw ⟨v, hv⟩
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, A, ℓ] using this
      have hg : g f ∈ Submodule.span ℂ (s : Set (J → ℂ)) := by
        rw [hspan]
        exact Submodule.subset_span ⟨f, hf, rfl⟩
      have := hle hg
      simpa [ℓ, g] using this
    · intro hw
      funext v
      obtain ⟨f, hf, hfv⟩ := hsS v.2
      have := hw f hf
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, A, Matrix.of_apply, Pi.zero_apply]
      rw [← hfv]
      simpa [g] using this
  have hkerT : LinearMap.ker A.mulVecLin = T := by
    ext w
    exact hker w
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hrange : Module.finrank ℂ (LinearMap.range A.mulVecLin) = Fintype.card s := by
    have : A.rank = Fintype.card s := by
      rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hAli]
    exact this
  rw [hrange, hkerT, hTd, Module.finrank_fintype_fun_eq_card, Fintype.card_congr e,
    Fintype.card_fin] at hrn
  have hcard : Fintype.card s = c := by omega
  let σ : Fin c ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ i, ∃ f ∈ P, g f = (σ i : J → ℂ) := fun i => by
    obtain ⟨f, hf, hfv⟩ := hsS (σ i).2
    exact ⟨f, hf, hfv⟩
  choose f hfP hfg using hmem
  refine ⟨f, hfP, ?_⟩
  have hfam : (fun i => grad (fun j => z₀ (e.symm j)) (map (Int.castRingHom ℂ) (rename e (f i)))) =
      (LinearEquiv.funCongrLeft ℂ ℂ e.symm).toLinearMap ∘ (fun i => (σ i : J → ℂ)) := by
    funext i j
    rw [gbap_grad_rename]
    show g (f i) (e.symm j) = (σ i : J → ℂ) (e.symm j)
    rw [hfg i]
  rw [hfam]
  exact (hsli.comp σ σ.injective).map' _ (LinearEquiv.ker _)

theorem gbap_withBot_eq {x : WithBot ℕ∞} {d a : ℕ}
    (h : x + (a : WithBot ℕ∞) = ((d + a : ℕ) : WithBot ℕ∞)) : x = (d : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.bot_add] at h
    exact WithBot.bot_ne_coe h
  | coe y =>
    have h' : y + (a : ℕ∞) = ((d + a : ℕ) : ℕ∞) := by exact_mod_cast h
    have hy : y = (d : ℕ∞) := by
      induction y using ENat.recTopCoe with
      | top =>
        exfalso
        rw [top_add] at h'
        exact ENat.coe_ne_top _ h'.symm
      | coe y =>
        norm_cast at h' ⊢
        omega
    rw [hy]
    rfl

theorem gbap_van_map {R : Type*} [CommRing R] {n : ℕ} (φ : R →+* MvPolynomial (Fin n) ℂ)
    (I : Ideal R) (w : Fin n → ℂ) :
    (∀ g ∈ I.map φ, eval w g = 0) ↔ ∀ g ∈ I, eval w (φ g) = 0 := by
  constructor
  · intro h g hg
    exact h _ (Ideal.mem_map_of_mem φ hg)
  · intro h g hg
    have hle : I.map φ ≤ RingHom.ker (eval w) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact h x hx
    exact hle hg

theorem gbap_map_map_int {σ : Type*} (g : MvPolynomial σ ℤ) :
    map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) g) = map (Int.castRingHom ℂ) g := by
  rw [map_map]
  congr 1

theorem gbap_surj_of_li {n c : ℕ} (F : Fin c → MvPolynomial (Fin n) ℂ) (p : Fin n → ℂ)
    (hli : LinearIndependent ℂ (fun i => grad p (F i))) :
    Function.Surjective (fun v : Fin n → ℂ => fun i => ∑ j, eval p (pderiv j (F i)) * v j) := by
  let M : Matrix (Fin c) (Fin n) ℂ := Matrix.of fun i j => eval p (pderiv j (F i))
  have hli' : LinearIndependent ℂ M.row := hli
  have hrank : M.rank = c := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hli', Fintype.card_fin]
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hrank
  intro y
  obtain ⟨v, hv⟩ := LinearMap.range_eq_top.1 htop y
  exact ⟨v, by rw [← hv]; rfl⟩

theorem gbap_cut {J : Type} [Fintype J] {D c : ℕ} (e : J ≃ Fin (D + 1 + c))
    (P : Ideal (MvPolynomial J ℤ)) [P.IsPrime]
    (hhor : ∀ m : ℤ, (C m : MvPolynomial J ℤ) ∈ P → m = 0)
    (hdim : ringKrullDim (MvPolynomial J ℤ ⧸ P) = ((D + 1 + 1 : ℕ) : WithBot ℕ∞))
    (z₀ : J → ℂ) (hz₀ : ∀ f ∈ P, eval z₀ (map (Int.castRingHom ℂ) f) = 0)
    (f : Fin c → MvPolynomial J ℤ) (hfP : ∀ i, f i ∈ P)
    (hli : LinearIndependent ℂ
      (fun i => grad (fun j => z₀ (e.symm j)) (map (Int.castRingHom ℂ) (rename e (f i))))) :
    ∃ (F : Fin c → MvPolynomial (Fin (D + 1 + c)) ℂ) (h : MvPolynomial (Fin (D + 1 + c)) ℂ),
      LinearIndependent ℂ (fun i => grad (fun j => z₀ (e.symm j)) (F i)) ∧
      eval (fun j => z₀ (e.symm j)) h ≠ 0 ∧
      ∀ w : Fin (D + 1 + c) → ℂ, eval w h ≠ 0 →
        ((∀ i, eval w (F i) = 0) ↔
          ∀ g ∈ P, eval (fun j => w (e j)) (map (Int.castRingHom ℂ) g) = 0) := by
  classical
  set fe : MvPolynomial J ℤ ≃+* MvPolynomial (Fin (D + 1 + c)) ℤ :=
    (renameEquiv ℤ e).toRingEquiv with hfe
  have hfe_apply : ∀ g, (fe : MvPolynomial J ℤ →+* MvPolynomial (Fin (D + 1 + c)) ℤ) g = rename e g :=
    fun g => rfl
  have hfe_symm : ∀ g, fe.symm g = rename e.symm g := fun g => rfl
  set P' : Ideal (MvPolynomial (Fin (D + 1 + c)) ℤ) :=
    P.map (fe : MvPolynomial J ℤ →+* MvPolynomial (Fin (D + 1 + c)) ℤ) with hP'
  have hP'mem : ∀ g, g ∈ P' ↔ rename e.symm g ∈ P := by
    intro g
    rw [hP', Ideal.map_comap_of_equiv, Ideal.mem_comap]
    rfl
  haveI : P'.IsPrime := by
    rw [hP', Ideal.map_comap_of_equiv]
    infer_instance
  have hP'hor : ∀ m : ℤ, (C m : MvPolynomial (Fin (D + 1 + c)) ℤ) ∈ P' → m = 0 := by
    intro m hm
    rw [hP'mem, rename_C] at hm
    exact hhor m hm
  have hdim' : ringKrullDim (MvPolynomial (Fin (D + 1 + c)) ℤ ⧸ P') =
      ((D + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hdim]
    exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv P P' fe rfl)).symm
  obtain ⟨hQp, -, hQd⟩ := extQ_spec P' hP'hor
  haveI := hQp
  have hQdim : ringKrullDim (MvPolynomial (Fin (D + 1 + c)) ℚ ⧸ extQ P') =
      ((D + 1 : ℕ) : WithBot ℕ∞) := by
    rw [hdim'] at hQd
    exact gbap_withBot_eq (a := 1) (by exact_mod_cast hQd)
  set K := extC (extQ P') with hK
  have hKvan : ∀ w : Fin (D + 1 + c) → ℂ, (∀ g ∈ K, eval w g = 0) ↔
      ∀ g ∈ P, eval (fun j => w (e j)) (map (Int.castRingHom ℂ) g) = 0 := by
    intro w
    rw [hK, extC, gbap_van_map, extQ]
    constructor
    · intro H g hg
      have := H _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem (fe : MvPolynomial J ℤ →+* MvPolynomial (Fin (D + 1 + c)) ℤ) hg))
      rw [hfe_apply, gbap_map_map_int, map_rename, eval_rename] at this
      exact this
    · intro H g hg
      induction hg using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        have hy' := (hP'mem y).1 hy
        have := H _ hy'
        rw [gbap_map_map_int]
        have hyy : y = rename e (rename e.symm y) := by
          rw [rename_rename, Equiv.self_comp_symm, rename_id_apply]
        rw [hyy, map_rename, eval_rename]
        exact this
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
      | smul a x _ hx => rw [smul_eq_mul, map_mul, map_mul, hx, mul_zero]
  set p' : Fin (D + 1 + c) → ℂ := fun j => z₀ (e.symm j) with hp'
  have hp'e : (fun j => p' (e j)) = z₀ := by
    funext j
    simp [hp']
  have hp'K : ∀ g ∈ K, eval p' g = 0 := by
    rw [hKvan, hp'e]
    exact hz₀
  have hKle : K ≤ ptIdeal p' := fun g hg => RingHom.mem_ker.2 (hp'K g hg)
  obtain ⟨𝔮, h𝔮min, h𝔮le⟩ := Ideal.exists_minimalPrimes_le hKle
  haveI : 𝔮.IsPrime := h𝔮min.1.1
  have hd𝔮 := ringKrullDim_of_mem_minimalPrimes_extC (extQ P') 𝔮 h𝔮min
  have hht := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field ℂ (D + 1 + c) 𝔮
  rw [hd𝔮, hQdim] at hht
  have hht' : (𝔮.height : WithBot ℕ∞) = (c : WithBot ℕ∞) :=
    gbap_withBot_eq (a := D + 1) (by rw [hht]; congr 1; omega)
  have hhtc : 𝔮.height ≤ c := by
    have : 𝔮.height = (c : ℕ∞) := by exact_mod_cast hht'
    rw [this]
  set F0 : Fin c → MvPolynomial (Fin (D + 1 + c)) ℂ :=
    fun i => map (Int.castRingHom ℂ) (rename e (f i)) with hF0
  have hF0K : ∀ i, F0 i ∈ K := by
    intro i
    have h1 : rename e (f i) ∈ P' :=
      Ideal.mem_map_of_mem (fe : MvPolynomial J ℤ →+* MvPolynomial (Fin (D + 1 + c)) ℤ) (hfP i)
    have := Ideal.mem_map_of_mem (map (algebraMap ℚ ℂ))
      (Ideal.mem_map_of_mem (map (Int.castRingHom ℚ)) h1)
    rw [gbap_map_map_int] at this
    exact this
  have hreg := isRegularLocalRing_of_jacobian K p' hp'K F0 hF0K hli ⟨𝔮, h𝔮min, h𝔮le, hhtc⟩
  haveI := hreg.1
  have hcc : D + 1 + c - (D + 1) = c := by omega
  obtain ⟨-, F', hF'K, hF'li, h, hh, hspan⟩ :=
    exists_jacobian_cut K p' (D + 1) (by rw [hreg.2]; congr 2; omega)
  refine ⟨fun i => F' (Fin.cast hcc.symm i), h, ?_, hh, ?_⟩
  · exact hF'li.comp _ (Fin.cast_injective _)
  · intro w hw
    rw [← hKvan]
    constructor
    · intro H g hg
      have hsp : Ideal.span (Set.range F') ≤ RingHom.ker (eval w) := by
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        have := H (Fin.cast hcc j)
        simp only [Fin.cast_cast, Fin.cast_eq_self] at this
        exact RingHom.mem_ker.2 this
      have := RingHom.mem_ker.1 (hsp (hspan g hg))
      rw [map_mul] at this
      exact (mul_eq_zero.1 this).resolve_left hw
    · intro H i
      exact H _ (hF'K _)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
