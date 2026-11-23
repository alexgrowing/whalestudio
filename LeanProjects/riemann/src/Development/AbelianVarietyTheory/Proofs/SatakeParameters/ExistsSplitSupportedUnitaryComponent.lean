import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitOnto

section Generic

variable {A : Type} [CommRing A] {n : ℕ}

def adj (c : A →+* A) (G H X : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A := H * (X.map c)ᵀ * G

variable {c : A →+* A} {G H : Matrix (Fin n) (Fin n) A}

theorem adj_add (X Y : Matrix (Fin n) (Fin n) A) : adj c G H (X + Y) = adj c G H X + adj c G H Y := by
  simp only [adj, Matrix.map_add _ (map_add c), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem adj_smul (a : A) (X : Matrix (Fin n) (Fin n) A) : adj c G H (a • X) = c a • adj c G H X := by
  have : (a • X).map c = c a • X.map c := by
    ext i j
    simp
  simp only [adj, this, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem adj_one (h : G * H = 1) : adj c G H 1 = 1 := by
  rw [adj, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one, mul_eq_one_comm.1 h]

theorem adj_mul (h : G * H = 1) (X Y : Matrix (Fin n) (Fin n) A) :
    adj c G H (X * Y) = adj c G H Y * adj c G H X := by
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc G H, h, Matrix.one_mul]

theorem adj_adj (hc : ∀ a, c (c a) = a) (h : G * H = 1) (hG : (G.map c)ᵀ = G) (X : Matrix (Fin n) (Fin n) A) :
    adj c G H (adj c G H X) = X := by
  have h' : H * G = 1 := mul_eq_one_comm.1 h
  have h1 : (H.map c)ᵀ * G = 1 := by
    conv_lhs => rw [← hG]
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one]
  have h2 : (((X.map c)ᵀ).map c)ᵀ = X := by
    ext i j
    exact hc _
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul, h2, hG, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [← Matrix.mul_assoc, h', Matrix.one_mul]

theorem exists_unitary (hc : ∀ a, c (c a) = a) (h : G * H = 1) (hG : (G.map c)ᵀ = G) {e : A} (he : e * e = e)
    (he' : e * c e = 0) (M M' : Matrix (Fin n) (Fin n) A) (hM : e • (M' * M) = e • (1 : Matrix (Fin n) (Fin n) A)) :
    ∃ g : GL (Fin n) A, (g.1.map c)ᵀ * G * g.1 = G ∧ (e + c e) • (g.1 - 1) = g.1 - 1 ∧ e • g.1 = e • M := by
  have hee : c e * c e = c e := by rw [← map_mul, he]
  have he2 : c e * e = 0 := by rw [mul_comm, he']
  set f := 1 - e - c e with hf
  have hcf : c f = f := by rw [hf, map_sub, map_sub, map_one, hc]; ring
  have h1 : e * f = 0 := by rw [hf]; linear_combination -he - he'
  have h2 : c e * f = 0 := by rw [hf]; linear_combination -hee - he'
  have h3 : f * e = 0 := by rw [mul_comm, h1]
  have h4 : f * c e = 0 := by rw [mul_comm, h2]
  have h5 : f * f = f := by linear_combination f * hf - h3 - h4
  set g := e • M + c e • adj c G H M' + f • (1 : Matrix (Fin n) (Fin n) A) with hg
  have hadj : adj c G H g = e • M' + c e • adj c G H M + f • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [hg, adj_add, adj_add, adj_smul, adj_smul, adj_smul, adj_adj hc h hG, adj_one h, hc, hcf, add_comm (c e • _)]
  have hM' : c e • (adj c G H M * adj c G H M') = c e • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [← adj_mul h, ← adj_smul, hM, adj_smul, adj_one h]
  have hinv : adj c G H g * g = 1 := by
    rw [hadj, hg]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, he, he', hee, he2,
      h1, h2, h3, h4, h5, zero_smul, add_zero, zero_add, Matrix.mul_one, hM, hM']
    rw [← add_smul, ← add_smul, hf]
    simp
  refine ⟨⟨g, adj c G H g, mul_eq_one_comm.1 hinv, hinv⟩, ?_, ?_, ?_⟩
  · change (g.map c)ᵀ * G * g = G
    have := congrArg (G * ·) hinv
    simpa only [adj, ← Matrix.mul_assoc, h, Matrix.one_mul, Matrix.mul_one] using this
  · change (e + c e) • (g - 1) = g - 1
    have h6 : f • g = f • (1 : Matrix (Fin n) (Fin n) A) := by
      simp only [hg, smul_add, smul_smul, h3, h4, h5, zero_smul, zero_add]
    have h7 : e + c e = 1 - f := by rw [hf]; ring
    rw [h7, sub_smul, one_smul, smul_sub, h6, sub_self, sub_zero]
  · change e • g = e • M
    simp only [hg, smul_add, smul_smul, he, he', h1, zero_smul, add_zero]

end Generic

variable {D : D7}

theorem cA_cA (z : Formalism.L2.Theta.AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]

theorem gram_det_ne (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    have hx : x = ∑ i, V.frame.repr x i • V.frame i := (V.frame.sum_repr x).symm
    rw [hx, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : ∑ j, V.gram i j * v j = 0 := congr_fun h0 i
    have h2 : V.hT (V.frame i) (V.frame.equivFun.symm v) = ∑ j, V.gram i j * v j := by
      rw [Module.Basis.equivFun_symm_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]; rfl
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h2, h1, smul_zero]
  exact V.frame.equivFun.symm.injective (this.trans (map_zero _).symm)

theorem gram_mul_inv (V : HSp D) : V.gram.map (incA D) * V.gram⁻¹.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem gram_conj (V : HSp D) : ((V.gram.map (incA D)).map (cA D))ᵀ = V.gram.map (incA D) := by
  ext i j
  have h : star (V.gram j i) = V.gram i j := LinearMap.isSymm_def.1 V.herm _ _
  exact congrArg (incA D) h

theorem exists_suppAt_rho_eq : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β x : GL (Fin V.rank) (Fv D.host.F v)), ∃ g : GA D V, SuppAt e V g ∧ rho V π β g = x := by
  intro D e v π he hπ V β x
  obtain ⟨he1, he2, -⟩ := he
  obtain ⟨hs, hk, -, -⟩ := hπ
  have key : ∀ a b, π a = π b ↔ e * a = e * b := fun a b => by
    rw [← sub_eq_zero, ← map_sub, hk, mul_sub, sub_eq_zero]
  have keyM : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (AE D), X.map π = Y.map π ↔ e • X = e • Y := fun X Y => by
    simp only [← Matrix.ext_iff, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, key]
  have lift : ∀ Z : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v),
      ∃ X : Matrix (Fin V.rank) (Fin V.rank) (AE D), X.map π = Z := fun Z => by
    choose X hX using fun i j => hs (Z i j)
    exact ⟨Matrix.of X, Matrix.ext hX⟩
  obtain ⟨M, hM⟩ := lift (β * x * β⁻¹).1
  obtain ⟨M', hM'⟩ := lift ((β * x * β⁻¹)⁻¹).1
  obtain ⟨g, h1, h2, h3⟩ := exists_unitary (c := cA D) cA_cA (gram_mul_inv V) (gram_conj V) he1 he2 M M' (by
    rw [← keyM, Matrix.map_mul, hM, hM', Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  let g' : HR (AF D.host.F) D.sp.cm.sig V.gram := ⟨g, h1⟩
  refine ⟨g', fun i j => congrFun (congrFun h2 i) j, Units.ext ?_⟩
  refine (rho_val V π β g').trans ?_
  change (β⁻¹).1 * g.1.map π * β.1 = x.1
  rw [(keyM _ _).2 h3, hM, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group

end GlobalTheory.SplitOnto
