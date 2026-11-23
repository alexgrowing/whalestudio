import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BadPlacesGoodCoefficients
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResSConjGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OToSAlgebraMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameMove

open Formalism.UG (bc cT)

theorem exists_glue {R : Type} [CommRing R] {n : ℕ} (ε : R) (hε : ε * ε = ε) (A : GL (Fin n) R) :
    ∃ y : GL (Fin n) R, y.val = (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) + ε • A.val := by
  have key : ∀ M N : Matrix (Fin n) (Fin n) R, M * N = 1 →
      ((1 - ε) • (1 : Matrix (Fin n) (Fin n) R) + ε • M) * ((1 - ε) • (1 : Matrix (Fin n) (Fin n) R) + ε • N) = 1 := by
    intro M N h
    have h1 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hε
    have h2 : (1 - ε) * ε = 0 := by linear_combination -hε
    have h3 : ε * (1 - ε) = 0 := by linear_combination -hε
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, h1, h2, h3, hε,
      Matrix.one_mul, Matrix.mul_one, zero_smul, add_zero, zero_add, h]
    rw [← add_smul, sub_add_cancel, one_smul]
  exact ⟨⟨_, _, key _ _ A.mul_inv, key _ _ A.inv_mul⟩, rfl⟩

theorem bc_glue_zero {R k : Type} [CommRing R] [CommRing k] {n : ℕ} {ε : R} {A y : GL (Fin n) R}
    (hy : y.val = (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) + ε • A.val) (φ : R →+* k) (h : φ ε = 0) :
    bc φ y = 1 := by
  ext i j
  show φ (y.val i j) = (1 : Matrix (Fin n) (Fin n) k) i j
  rw [hy]
  by_cases hij : i = j <;> simp [h, Matrix.one_apply, hij]

theorem bc_glue_one {R k : Type} [CommRing R] [CommRing k] {n : ℕ} {ε : R} {A y : GL (Fin n) R}
    (hy : y.val = (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) + ε • A.val) (φ : R →+* k) (h : φ ε = 1) :
    bc φ y = bc φ A := by
  ext i j
  show φ (y.val i j) = φ (A.val i j)
  rw [hy]
  simp [h]

theorem exists_rev (R : Type) [CommRing R] (n : ℕ) :
    ∃ W : GL (Fin n) R, ∀ (M : Matrix (Fin n) (Fin n) R) (i j : Fin n),
      ((W⁻¹).val * M * W.val) i j = M i.rev j.rev := by
  have h : ∀ M : Matrix (Fin n) (Fin n) R,
      (Fin.revPerm (n := n)).toPEquiv.toMatrix * M * (Fin.revPerm (n := n)).toPEquiv.toMatrix
        = M.submatrix Fin.rev Fin.rev := by
    intro M
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    rfl
  have h1 : ((Fin.revPerm (n := n)).toPEquiv.toMatrix : Matrix (Fin n) (Fin n) R) *
      (Fin.revPerm (n := n)).toPEquiv.toMatrix = 1 := by
    have := h 1
    rw [Matrix.mul_one] at this
    rw [this]
    exact Matrix.submatrix_one_equiv (Fin.revPerm (n := n))
  exact ⟨⟨_, _, h1, h1⟩, fun M i j => congrFun (congrFun (h M) i) j⟩

theorem conj_gram {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (β G h : GL (Fin n) A) (hG : G.val = cT σ β.val * J * β.val)
    (hx : β * h * β⁻¹ ∈ Formalism.UG.UJ σ J) :
    (G * h * G⁻¹).val = cT σ (h⁻¹).val := by
  have hx' : cT σ (β * h * β⁻¹).val * J * (β * h * β⁻¹).val = J := hx
  have e1 : cT σ h.val * G.val * h.val = G.val := by
    have e : (β * h * β⁻¹).val * β.val = β.val * h.val := by
      rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
    calc cT σ h.val * G.val * h.val = cT σ (β.val * h.val) * J * (β.val * h.val) := by
          rw [hG, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ β.val * (cT σ (β * h * β⁻¹).val * J * (β * h * β⁻¹).val) * β.val := by
          rw [← e, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = G.val := by rw [hx', hG]
  have e2 : cT σ (h⁻¹).val * cT σ h.val = 1 := by
    rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
  calc (G * h * G⁻¹).val = (cT σ (h⁻¹).val * cT σ h.val) * (G.val * h.val * (G⁻¹).val) := by
        rw [e2, Matrix.one_mul]; rfl
    _ = cT σ (h⁻¹).val * ((cT σ h.val * G.val * h.val) * (G⁻¹).val) := by simp only [Matrix.mul_assoc]
    _ = cT σ (h⁻¹).val := by rw [e1, Units.mul_inv, Matrix.mul_one]

theorem conj_gram_sub {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (O : Subring A) (J : Matrix (Fin n) (Fin n) A)
    (β : GL (Fin n) A) (G h : GL (Fin n) O) (hG : (bc O.subtype G).val = cT σ β.val * J * β.val)
    (hx : β * bc O.subtype h * β⁻¹ ∈ Formalism.UG.UJ σ J) (i j : Fin n) :
    (((G * h * G⁻¹).val i j : O) : A) = σ ((h⁻¹).val j i : O) := by
  have c := conj_gram σ J β (bc O.subtype G) (bc O.subtype h) hG hx
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul] at c
  exact congrFun (congrFun c i) j

theorem bc_conj_zero {R k : Type} [CommRing R] [CommRing k] {n : ℕ} {ε : R} {A y : GL (Fin n) R}
    (hy : y.val = (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) + ε • A.val) (φ : R →+* k) (h : φ ε = 0)
    (g : GL (Fin n) R) : bc φ (y⁻¹ * g * y) = bc φ g := by
  rw [map_mul, map_mul, map_inv, bc_glue_zero hy φ h]
  simp

theorem bc_conj_one {R k : Type} [CommRing R] [CommRing k] {n : ℕ} {ε : R} {G W y : GL (Fin n) R}
    (hW : ∀ (M : Matrix (Fin n) (Fin n) R) (i j : Fin n), ((W⁻¹).val * M * W.val) i j = M i.rev j.rev)
    (hy : y.val = (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) + ε • (G⁻¹ * W).val) (φ : R →+* k) (h : φ ε = 1)
    (g : GL (Fin n) R) (i j : Fin n) :
    (bc φ (y⁻¹ * g * y)).val i j = φ ((G * g * G⁻¹).val i.rev j.rev) := by
  have e2 : bc φ (y⁻¹ * g * y) = bc φ (W⁻¹ * (G * g * G⁻¹) * W) := by
    have : W⁻¹ * (G * g * G⁻¹) * W = (G⁻¹ * W)⁻¹ * g * (G⁻¹ * W) := by group
    rw [this, map_mul, map_mul, map_inv, bc_glue_one hy φ h, map_mul _ (_ * g), map_mul _ _ g, map_inv]
  rw [e2, ← hW (G * g * G⁻¹).val i j]
  rfl

theorem bc_inv_apply {R k : Type} [CommRing R] [CommRing k] {n : ℕ} (φ : R →+* k) (g : GL (Fin n) R)
    (i j : Fin n) : ((bc φ g)⁻¹).val i j = φ ((g⁻¹).val i j) := by
  rw [← map_inv]; rfl

theorem redFn_move {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y h : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (w : Pl E) :
    redFn (β * intGL F E n y) w (frGL β h) = bc (resS F w) (y⁻¹ * h * y) := by
  have e : frGL β h = frGL (β * intGL F E n y) (y⁻¹ * h * y) := by
    show β * intGL F E n h * β⁻¹ = (β * intGL F E n y) * intGL F E n (y⁻¹ * h * y) * (β * intGL F E n y)⁻¹
    rw [map_mul, map_mul, map_inv]; group
  rw [e, redFn_frGL]

theorem exists_move_core {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (σ : E ⊗[F] Formalism.L2.Herm.Af F →+* E ⊗[F] Formalism.L2.Herm.Af F) (J : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (G : GL (Fin n) (Formalism.L2.Herm.intAf F E))
    (hG : (intGL F E n G).val = cT σ β.val * J * β.val) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ y : GL (Fin n) (Formalism.L2.Herm.intAf F E), ∀ x ∈ Formalism.UG.UJ σ J, x ∈ St β →
      ∀ (w' : Pl E) (v : HeightOneSpectrum (𝓞 F)), w'.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal →
      (v ∉ S → redFn (β * intGL F E n y) w' x = redFn β w' x) ∧
      (v ∈ S → ∀ (i j : Fin n), ∃ s t : Formalism.L2.Herm.intAf F E, t.1 = σ s.1 ∧
        (redFn (β * intGL F E n y) w' x).val i j = resS F w' t ∧
        ∀ w : Pl E, ((redFn β w x)⁻¹).val j.rev i.rev = resS F w s) := by
  obtain ⟨ε, hε, hres⟩ := GlobalTheory.AdeleIdem.exists_idem F E S
  obtain ⟨W, hW⟩ := exists_rev (Formalism.L2.Herm.intAf F E) n
  obtain ⟨y, hy⟩ := exists_glue ε hε (G⁻¹ * W)
  refine ⟨y, ?_⟩
  intro x hxU hx w' v hv
  obtain ⟨h, hh⟩ := hx
  subst hh
  refine ⟨fun hS => ?_, fun hS i j => ⟨_, _, conj_gram_sub σ _ J β G h hG hxU i.rev j.rev, ?_, fun w => ?_⟩⟩
  · rw [redFn_move, redFn_frGL, bc_conj_zero hy _ ((hres w' v hv).2 hS)]
  · rw [redFn_move, bc_conj_one hW hy _ ((hres w' v hv).1 hS)]
  · rw [redFn_frGL, bc_inv_apply]

theorem exists_frame_move : ∀ (D : D7) (n : ℕ) (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (EAf D)) (G : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)), (intGL D.host.F D.host.E n G).val = Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) β.val * J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * β.val → ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∃ y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E), ∀ x ∈ UA D.sp.cm J, x ∈ St β → ∀ (w' : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)), w'.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal → (v ∉ S → redFn (β * intGL D.host.F D.host.E n y) w' x = redFn β w' x) ∧ (v ∈ S → ∀ w : Pl D.host.E, IsConjPl w w' → ∀ (p : ℕ) (e : kP w ≃+* ZMod p) (e' : ZMod p ≃+* kP w') (i j : Fin n), (redFn (β * intGL D.host.F D.host.E n y) w' x).val i j = e' (e (((redFn β w x)⁻¹).val j.rev i.rev))) := by
  intro D n J β G hG S
  refine (exists_move_core _ _ β G hG S).imp fun y hy x hxU hx w' v hv => ?_
  refine ⟨(hy x hxU hx w' v hv).1, fun hS w hw p ep ep' i j => ?_⟩
  obtain ⟨s, t, hst, h1, h2⟩ := (hy x hxU hx w' v hv).2 hS i j
  exact h1.trans ((GlobalTheory.ResConjPlace.resS_conj D w w' hw s t hst p ep ep').trans (congrArg (fun z => ep' (ep z)) (h2 w).symm))

end GlobalTheory.FrameMove
