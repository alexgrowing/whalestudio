import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalBasisAlong

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.Recombine
open GlobalTheory.FrameGen

variable {Z : Scheme.{0}} {G : Over Z} {L : LB G.left} {N : ℕ}

theorem exists_lin (hL : L.IsLB) {T T' : Over Z} (h : T' ⟶ T) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T))
    (c : Fin n → Γ(T'.left, ⊤)) : ∃ s, Lin G L N h b c s := by
  choose b' hb' using fun i => exists_pull hL h (b i)
  refine ⟨SectionLimit.linSec (fun i => (fst T' G).left.appTop.hom (c i)) b', fun z J hJ => ?_⟩
  refine (SectionScalarValuation.sval_lin (s := SectionLimit.linSec (fun i => (fst T' G).left.appTop.hom (c i)) b')
    (fun i => (fst T' G).left.appTop.hom (c i)) b' (fun _ => rfl) (𝟙 _) z hJ).trans
    (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ ?_)
  · exact (gs_pull (𝟙 _) (fst T' G).left z ⊤ trivial (c i)).trans (by rw [Category.id_comp])
  · exact (hb' i _ (𝟙 _) z J hJ).trans (by rw [Category.id_comp]; rfl)

section
variable {T T₁ T₂ T₃ : Over Z} {m n l : ℕ} {h₁ : T ⟶ T₁} {a : Fin m → LB.Sec (LPow G L (N : ℤ) T₁)} {h₂ : T ⟶ T₂}
  {b : Fin n → LB.Sec (LPow G L (N : ℤ) T₂)} {h₃ : T ⟶ T₃} {c : Fin l → LB.Sec (LPow G L (N : ℤ) T₃)}

theorem rel_id_iff (hL : L.IsLB) {a : Fin m → LB.Sec (LPow G L (N : ℤ) T)} {M : Matrix (Fin m) (Fin n) Γ(T.left, ⊤)} :
    Rel G L N (𝟙 _) a h₂ b M ↔ ∀ k, Lin G L N h₂ b (M k) (a k) := by
  constructor
  · intro H k z J hJ
    have := H k _ (𝟙 _) z J hJ
    simp only [Category.id_comp, ← gs_top, id_whiskerRight, Over.id_left] at this
    exact this
  · intro H k Y r z J hJ
    rw [id_whiskerRight, Over.id_left, Category.comp_id]
    exact lin_all hL (H k) r z hJ

theorem rel_inv {M : Matrix (Fin m) (Fin n) Γ(T.left, ⊤)} {V : Matrix (Fin n) (Fin m) Γ(T.left, ⊤)}
    (H : Rel G L N h₁ a h₂ b M) (e : V * M = (1 : Matrix (Fin n) (Fin n) Γ(T.left, ⊤))) : Rel G L N h₂ b h₁ a V := by
  intro k Y r z J hJ
  rw [Rel.refl (h₁ := h₂) (a := b) k Y r z J hJ, ← e]
  simp only [H _ Y r z J hJ, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

theorem basisAlong_of_rel (hL : L.IsLB) {a : Fin n → LB.Sec (LPow G L (N : ℤ) T₁)} {M V : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)}
    (hb : BasisAlong G L N h₂ b)
    (H : Rel G L N h₁ a h₂ b M) (e : V * M = 1) (e' : M * V = 1) : BasisAlong G L N h₁ a := by
  intro s
  obtain ⟨P, hP⟩ := exists_rel hL hb (𝟙 _) (fun _ : Fin 1 => s)
  have key : ∀ c, Lin G L N h₁ a c s → Matrix.of (fun _ : Fin 1 => c) = P * V := fun c hc => by
    have r : Rel G L N (𝟙 _) (fun _ : Fin 1 => s) h₁ a (Matrix.of fun _ : Fin 1 => c) := (rel_id_iff hL).2 fun _ => hc
    rw [hP.unique hL hb (r.trans H), Matrix.mul_assoc, e', Matrix.mul_one]
  exact ⟨(P * V) 0, (rel_id_iff hL).1 (hP.trans (rel_inv H e)) 0, fun c hc => congrFun (key c hc) 0⟩

theorem exists_common (hL : L.IsLB) {b : Fin m → LB.Sec (LPow G L (N : ℤ) T₂)} {M} (H : Rel G L N h₁ a h₃ c M)
    (H' : Rel G L N h₂ b h₃ c M) (k : Fin m) :
    ∃ s, Lin G L N h₁ (fun _ : Fin 1 => a k) (fun _ => 1) s ∧ Lin G L N h₂ (fun _ : Fin 1 => b k) (fun _ => 1) s := by
  obtain ⟨s, hs⟩ := exists_lin hL h₁ (fun _ : Fin 1 => a k) (fun _ => 1)
  refine ⟨s, hs, fun z J hJ => (hs z J hJ).trans ?_⟩
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  have := (H k _ (𝟙 _) z J hJ).trans (H' k _ (𝟙 _) z J hJ).symm
  rw [Category.id_comp, Category.id_comp] at this
  exact congrArg _ this

theorem exists_common_pull (hL : L.IsLB) {b : Fin n → LB.Sec (LPow G L (N : ℤ) T₂)} {b' : Fin m → LB.Sec (LPow G L (N : ℤ) T₂)}
    {p : T₁ ⟶ T₃} {P : Matrix (Fin m) (Fin l) Γ(T₁.left, ⊤)} {U : Matrix (Fin m) (Fin n) Γ(T₂.left, ⊤)}
    {B : Matrix (Fin n) (Fin l) Γ(T.left, ⊤)} (r₁ : Rel G L N (𝟙 _) a p c P) (r₂ : Rel G L N (𝟙 _) b' (𝟙 _) b U)
    (r₃ : Rel G L N h₂ b h₃ c B) (e₁ : h₁ ≫ p = h₃) (e₂ : P.map h₁.left.appTop.hom = U.map h₂.left.appTop.hom * B)
    (k : Fin m) :
    ∃ s, Lin G L N h₁ (fun _ : Fin 1 => a k) (fun _ => 1) s ∧ Lin G L N h₂ (fun _ : Fin 1 => b' k) (fun _ => 1) s := by
  have r₄ := r₁.pull h₁
  have r₅ := r₂.pull h₂
  rw [Category.comp_id] at r₄ r₅
  rw [e₁, e₂] at r₄
  exact exists_common hL r₄ (r₅.trans r₃) k

end

abbrev fnHom (R : Type) [CommRing R] : R →+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem map_fnHom {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) :
    (M.map (fnHom R)).map (spMap f).appTop.hom = (M.map f).map (fnHom R') := by
  ext1 i j
  exact (congrArg (fun q => q.hom (M i j)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem exists_rel_id (hL : L.IsLB) {T T' : Over Z} (h : T' ⟶ T) {m n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T))
    (M : Matrix (Fin m) (Fin n) Γ(T'.left, ⊤)) : ∃ a, Rel G L N (𝟙 _) a h b M := by
  choose a ha using fun i => exists_lin hL h b (M i)
  exact ⟨a, (rel_id_iff hL).2 ha⟩

theorem map_inv_mul {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {n : ℕ} {U : Matrix (Fin n) (Fin n) R}
    (hU : IsUnit U.det) : U⁻¹.map f * U.map f = 1 ∧ U.map f * U⁻¹.map f = 1 :=
  ⟨Matrix.map_mul.symm.trans (by rw [Matrix.nonsing_inv_mul _ hU, Matrix.map_one _ (map_zero _) (map_one _)]),
    Matrix.map_mul.symm.trans (by rw [Matrix.mul_nonsing_inv _ hU, Matrix.map_one _ (map_zero _) (map_one _)])⟩

theorem map_fnHom_mul {R W F : Type} [CommRing R] [CommRing W] [CommRing F] (f : R →+* F) (g : W →+* F) {n : ℕ}
    {P : Matrix (Fin n) (Fin n) R} {U : Matrix (Fin n) (Fin n) W} {B : Matrix (Fin n) (Fin n) F}
    (e : P.map f = U.map g * B) : (P.map (fnHom R)).map (spMap f).appTop.hom =
      (U.map (fnHom W)).map (spMap g).appTop.hom * B.map (fnHom F) := by
  rw [map_fnHom, map_fnHom, e, Matrix.map_mul]

theorem exists_recombination : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left), L.IsLB → ∀ (N : ℕ) (K K₂ : Type) [Field K] [Field K₂] (x : Sp K ⟶ Z) (ie : K →+* K₂) (x₂ : Sp K₂ ⟶ Z), spMap ie ≫ x = x₂ → ∀ (n : ℕ) (τ : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))) (Φ : Matrix (Fin n) (Fin n) K₂), ∃ f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x₂)), ∀ (W : Type) [CommRing W] [IsDomain W] (gam : K₂ →+* FractionRing W) (χ : Sp W ⟶ Z) (h : spMap (gam.comp ie) ≫ x = jK W ≫ χ) (h₂ : spMap gam ≫ x₂ = jK W ≫ χ) (B : Matrix (Fin n) (Fin n) (FractionRing W)) (U : Matrix (Fin n) (Fin n) W), BasisBy G L N x (gam.comp ie) χ h τ B → IsUnit U.det → Φ.map gam = U.map (algebraMap W (FractionRing W)) * B → FrameAt G L N x₂ gam χ h₂ f := by
  intro Z G L hL N K K₂ _ _ x ie x₂ hx n τ Φ
  obtain ⟨f, r₁⟩ := exists_rel_id hL (Over.homMk (spMap ie) hx : Over.mk x₂ ⟶ Over.mk x) τ (Φ.map (fnHom K₂))
  refine ⟨f, fun W _ _ gam χ h h₂ B U H hU e => ?_⟩
  obtain ⟨b, hb, hB⟩ := H
  obtain ⟨b', r₂⟩ := exists_rel_id hL (𝟙 (Over.mk χ)) b (U.map (fnHom W))
  have r₃ : Rel G L N (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) b
      (Over.homMk (spMap (gam.comp ie)) h : Over.mk (jK W ≫ χ) ⟶ Over.mk x) τ (B.map (fnHom (FractionRing W))) :=
    rel_of_lin hL fun k => (hB k).imp fun _ H => H.symm
  exact ⟨b', basisAlong_of_rel hL hb r₂ (map_inv_mul (fnHom W) hU).1 (map_inv_mul (fnHom W) hU).2,
    exists_common_pull hL r₁ r₂ r₃ (Over.OverMorphism.ext (spMap_comp' ie gam).symm) (map_fnHom_mul gam _ e)⟩

end GlobalTheory.Recombine
end
