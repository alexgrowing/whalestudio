import Development.WeilBound.ThetaLifts.TowerModels.PlanePair
import Development.WeilBound.ThetaLifts.TowerModels.PlaneIso
import Development.WeilBound.ThetaLifts.TowerModels.PlaneBas
import Development.WeilBound.ThetaLifts.TowerModels.PlaneComp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified

noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

structure IsEps (σ : E →ₐ[F] E) (B : Base F E) (ε : E) (κ : ℂ) (D : Submodule (𝓞 E) E) {n : ℕ} (X : Spc F E n)
    (r s : ℕ) : Prop where
  herm : ∀ i j, σ (X.J j i) = ε * X.J i j
  sig : ∀ w, HasSig (κ • X.J.map (B.emb w).1) r s
  lat : X.L.IsLattice E
  dual : ∀ y, y ∈ X.L ↔ ∀ x ∈ X.L, form σ X.J y x ∈ D
  cartan : ∀ w, IsCartan (κ • X.J.map (B.emb w).1) (X.θ w)
  bas : ∀ v : B.P, IsSplitBasis (B.τ v) X.L (X.bas v)

theorem exists_plane {B : Base F E} (hB : B.IsGood σ) {ε : E} (hε : ε = 1 ∨ ε = -1) {κ : ℂ} (hκ1 : κ * star κ = 1)
    (hκ : ∀ e : E →+* ℂ, star κ * e ε = κ) (D : Submodule (𝓞 E) E) (hD1 : (1 : E) ∈ D)
    (hDτ : ∀ v : B.P, ∀ c ∈ D, Valued.v (B.τ v c) ≤ 1) (n n₁ : ℕ) (hn : n = n₁ + 2) (hn₁ : 1 ≤ n₁) (Y : Spc F E n)
    (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (hY : IsEps σ B ε κ D Y r s) (i₀ i₁ : ℕ) (h01 : i₀ < i₁) (h1n : i₁ < n) :
    ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsEps σ B ε κ D (GlobalTheory.ThK.reS Y Y') r s ∧
      IsEps σ B ε κ D Y₁ (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁ := by
  classical
  have hcm : IsCMExt F E σ := hB.cm
  have hκ0 : κ ≠ 0 := left_ne_zero_of_mul_eq_one hκ1
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hεL : ∀ a ∈ Y.L, ε • a ∈ Y.L := fun a ha => by
    rcases hε with rfl | rfl
    · simpa using ha
    · simpa using ha
  have hdet : Y.J.det ≠ 0 := fun h0 => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    refine det_ne_zero_of_hasSig (hY.sig w) ?_
    rw [Matrix.det_smul, show (Y.J.map (B.emb w).1).det = (B.emb w).1 Y.J.det from (RingHom.map_det _ _).symm, h0,
      map_zero, mul_zero]
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
    haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hB.unram
    exact GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm inferInstance
  obtain ⟨x₀, hx₀, hx₀x₀⟩ := exists_isotropic hcm B.emb (by omega) hr hs hdet hε hY.herm hκ0 hκ hY.sig
  obtain ⟨x, y, hxx, hyy, hxy, hL, hP⟩ := exists_adapted_pair hcm hdet hε hY.herm D hD1 Y.L hY.lat hY.dual θ₀ hθ₀ B.P B.τ
    hDτ x₀ hx₀ hx₀x₀
  have hyx : form σ Y.J y x = ε := by
    have := form_swap hcm hY.herm x y
    rw [hxy, map_one] at this
    linear_combination -ε * this - form σ Y.J y x * hεε
  obtain ⟨ι, P, hPι, horth, hcomp⟩ := exists_compl (σ := σ) n n₁ Y.J x y hn hxx hyy hxy
    (by rw [hyx]; exact left_ne_zero_of_mul_eq_one hεε)
  have hsplit : ∀ z ∈ Y.L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ Y.L ∧ t • y ∈ Y.L ∧ ι *ᵥ u ∈ Y.L ∧
      z = s • x + ι *ᵥ u + t • y := by
    intro z hz
    obtain ⟨u, hu⟩ := hcomp (z - form σ Y.J z y • x - (ε * form σ Y.J z x) • y) (by
        rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, hxx, hyx]
        linear_combination -form σ Y.J z x * hεε) (by
        rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, hxy, hyy]; ring)
    have ht : (ε * form σ Y.J z x) • y ∈ Y.L := by rw [mul_smul]; exact hεL _ (hL z hz).1
    refine ⟨_, _, u, (hL z hz).2, ht, ?_, ?_⟩
    · rw [← hu]; exact Y.L.sub_mem (Y.L.sub_mem hz (hL z hz).2) ht
    · rw [← hu]; abel
  set L₁ := Y.L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E)) with hL₁def
  have hlat₁ : L₁.IsLattice E := isLattice_comap n n₁ Y.L ι P hPι hY.lat
  have hx0 : x ≠ 0 := by rintro rfl; simp [form] at hxy
  obtain ⟨𝔟, h𝔟⟩ := exists_ideal n Y.L hY.lat x hx0
  set J₁ := ιᵀ * Y.J * ι.map σ with hJ₁
  have hform₁ : ∀ u u', form σ J₁ u u' = form σ Y.J (ι *ᵥ u) (ι *ᵥ u') := form_gram Y.J ι
  let e : InfinitePlace F → E →+* ℂ := fun w => (B.emb w).1
  have hreal : ∀ w, HasSig (κ • J₁.map (e w)) (r - 1) (s - 1) ∧ ∃ θ θ₁, IsCartan (κ • Y.J.map (e w)) θ ∧
      IsCartan (κ • J₁.map (e w)) θ₁ ∧ θ * ι.map (e w) = ι.map (e w) * θ₁ ∧
      (κ • fun i => e w (y i)) = (2 : ℂ) • θ *ᵥ fun i => e w (x i) := fun w => by
    have cg : (ι.map (e w))ᵀ * (κ • Y.J.map (e w)) * (ι.map (e w)).map star = κ • J₁.map (e w) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, map_gram hcm]
    rw [← cg]
    refine real_plane _ _ _ _ (P.map (e w)) hn (map_herm hcm _ (hκ _) hY.herm) ?_ ?_ ?_ ?_ ?_ ?_ (hY.sig w)
    · rw [Matrix.smul_mulVec, dotProduct_smul, ← map_form hcm, hxx, map_zero, smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hyy, map_zero, smul_zero, smul_zero, smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hxy, map_one, smul_eq_mul, smul_eq_mul, mul_one, mul_comm, hκ1]
    · rw [Matrix.smul_mulVec, Matrix.mulVec_smul, map_orth hcm _ Y.J ι x (fun u => (horth u).1), smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
        map_orth hcm _ Y.J ι y (fun u => (horth u).2), smul_zero, smul_zero]
    · rw [← Matrix.map_mul, hPι, Matrix.map_one _ (map_zero _) (map_one _)]
  choose hsig₁ θ θ₁ hθ hθ₁ hθι hθx using hreal
  haveI := hlat₁
  have hb₁ : ∀ v : B.P, ∃ β, IsSplitBasis (B.τ v) L₁ β := fun v => exists_isSplitBasis (B.τ v) L₁ hcm
  choose β₁ hβ₁ using hb₁
  let bas₁ : ∀ v : Pl F, GL (Fin n₁) (Fv F v) := fun v => if h : v ∈ B.P then β₁ ⟨v, h⟩ else 1
  have hbas₁ : ∀ v : B.P, bas₁ v = β₁ v := fun v => by simp only [bas₁, dif_pos v.2]
  choose β hβ using fun v : B.P => exists_basis (B.τ v) n n₁ Y.L x y ι (β₁ v) i₀ i₁ hn h01 h1n hY.lat hsplit
    (hP v).1 (hP v).2 (hβ₁ v)
  let bas : ∀ v : Pl F, GL (Fin n) (Fv F v) := fun v => if h : v ∈ B.P then β ⟨v, h⟩ else Y.bas v
  have hbas : ∀ v : B.P, bas v = β v := fun v => by simp only [bas, dif_pos v.2]
  let Y₁ : Spc F E n₁ := ⟨J₁, L₁, θ₁, bas₁⟩
  let Y' : Spc F E n := ⟨Y.J, Y.L, θ, bas⟩
  refine ⟨Y', Y₁, ⟨x, y, ι, 𝔟⟩, ?_, ?_, ?_⟩
  · exact { herm := hY.herm, sig := hY.sig, lat := hY.lat, dual := hY.dual, cartan := hθ
            bas := fun v => by
              rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v]
              exact (hβ v).2 }
  · exact { herm := fun i j => by
              show σ (J₁ j i) = ε * J₁ i j
              rw [← form_single (σ := σ) J₁ j i, ← form_single (σ := σ) J₁ i j, hform₁, hform₁,
                form_swap hcm hY.herm]
            sig := hsig₁
            lat := hlat₁
            dual := fun u => by
              show u ∈ L₁ ↔ ∀ u' ∈ L₁, form σ J₁ u u' ∈ D
              refine ⟨fun hu u' hu' => ?_, fun H => ?_⟩
              · rw [hform₁]; exact (hY.dual _).1 hu _ hu'
              · show ι *ᵥ u ∈ Y.L
                refine (hY.dual _).2 fun z hz => ?_
                obtain ⟨_, _, u', -, -, hu', hz'⟩ := hsplit z hz
                rw [hz', form_add_right, form_add_right, form_smul_right, form_smul_right, (horth u).1,
                  (horth u).2, mul_zero, mul_zero, zero_add, add_zero, ← hform₁]
                exact H u' hu'
            cartan := hθ₁
            bas := fun v => by
              rw [show Y₁.bas v = β₁ v from hbas₁ v]
              exact hβ₁ v }
  · exact { rank := hn, xx := hxx, yy := hyy, xy := hxy, orth := horth, gram := rfl, low := fun u => Iff.rfl
            split := hsplit
            ideal := h𝔟
            cartan := fun w => ⟨hθι w, κ⁻¹ * 2, mul_ne_zero (inv_ne_zero hκ0) two_ne_zero, by
              rw [mul_smul]
              exact (eq_inv_smul_iff₀ hκ0).2 (hθx w)⟩
            bas := fun v i => by
              rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v, show Y₁.bas v = β₁ v from hbas₁ v]
              exact (hβ v).1 i }

theorem isHerm_iff {B : Base F E} {n : ℕ} {X : Spc F E n} {r s : ℕ} : X.IsHerm σ B r s ↔ IsEps σ B 1 1 (intE E) X r s :=
  ⟨fun h => ⟨by simpa using h.herm, by simpa using h.sig, h.lat, h.dual, by simpa using h.cartan, h.bas⟩,
    fun h => ⟨by simpa using h.herm, by simpa using h.sig, h.lat, h.dual, by simpa using h.cartan, h.bas⟩⟩

theorem isSkew_iff {B : Base F E} {n : ℕ} {X : Spc F E n} {r s : ℕ} :
    X.IsSkew σ B r s ↔ IsEps σ B (-1) Complex.I (codE E) X r s :=
  ⟨fun h => ⟨by simpa using h.skew, h.sig, h.lat, h.dual, h.cartan, h.bas⟩,
    fun h => ⟨by simpa using h.herm, h.sig, h.lat, h.dual, h.cartan, h.bas⟩⟩

end PositivityTheory.ThKG.Tow.Pln

end
