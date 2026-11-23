import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CastGLSymmBc

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

theorem colSpan_map {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (A g : Matrix (Fin k) (Fin k) K) :
    (colSpan R g).map ((Matrix.mulVecLin A).restrictScalars R) = colSpan R (A * g) := by
  simp only [colSpan, Submodule.map_span]
  congr 1
  rw [← Set.range_comp]
  congr 1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem prV_incl (w : HeightOneSpectrum (𝓞 F)) :
    (prV (E := E) w).comp (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) = inclE (F := F) (w.adicCompletion F) := by
  ext x
  simp [prV, inclE]

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ} {G : GAtP p}

theorem eQ_iw (A : LocAt F E n G) (v : Fin G.P.nV) :
    ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)).comp (A.iw v) = A.phE v := by
  ext x
  simp [LocAt.iw]

private theorem bc_bc_eq_bc_comp {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] {m : ℕ}
    (φ : R₂ →+* R₃) (ψ : R₁ →+* R₂) (x : GL (Fin m) R₁) : bc φ (bc ψ x) = bc (φ.comp ψ) x := by
  ext i j
  simp [bc]

theorem LocAt.isPt_smul (A : LocAt F E n G) (hA : A.ActB) (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (x κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : A.IsPt i g x) (γ : (G.lev i).Γ) (hκ : A.IsAway i γ κ) :
    A.IsPt i (fun v => (G.lev i).act v γ * g v)
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * x * κ⁻¹) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hκ1, hκ2⟩ := hκ
  refine ⟨fun w hw => ?_, fun v => ?_⟩
  · simp only [map_mul, map_inv, hx1 w hw, hκ2 w hw]
    group
  · have hP : bc (A.ph v) (bc (prV (E := E) (A.pl v).1)
        (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ))) = bc (A.phE v) (A.gamI i γ) := by
      rw [bc_bc_eq_bc_comp, bc_bc_eq_bc_comp, RingHom.comp_assoc, prV_incl, LocAt.phE]
    have hQ : bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F))
        (castGL A.rk (G.P.Qq v) ((G.lev i).act v γ)) =
          (bc (A.phE v) A.B)⁻¹ * bc (A.phE v) (A.gamI i γ) * bc (A.phE v) A.B := by
      rw [hA i v γ, bc_bc_eq_bc_comp, eQ_iw]
      simp only [map_mul, map_inv]
    simp only [map_mul, map_inv, hκ1 v, inv_one, mul_one, hP, hx2 v, hQ]
    group

theorem atInf_mul (emb : Tau → E →+* ℂ) (a b : Matrix (Fin n) (Fin n) E) (τ : Tau) :
    atInf emb (a * b) τ = atInf emb a τ * atInf emb b τ := by
  simp [atInf, Matrix.map_mul]

theorem CmpTie.val_equiv {S : StepLevel F E σ J T f bad} {emb : Tau → E →+* ℂ} {embLL : LL →+* ℂ} {tE : Tau → E →+* LL}
    {e : LL →+* G.Kf} {A : LocAt F E n G} {pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau}
    {V cls : Type} {embV : V → cls → Frames (gramC J emb) → ℂ} {yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    {cmp : V → G.Fn} (K : CmpTie S emb embLL tE G e A pos embV yc cmp)
    (htE : ∀ τ x, embLL (tE τ x) = emb τ x) (hBs : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1) (hA : A.ActB)
    (x : V) (i : G.comp) (L : G.P.Tup) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (γ : (G.lev i).Γ) (hγ : A.gamI i γ ∈ UJ (σ : E →+* E) J) (κ : S.U) (hκ : A.IsAway i γ κ.1)
    (c : cls) (γ₀ : GL (Fin n) E) (hγ₀ : γ₀ ∈ UJ (σ : E →+* E) J) (κ₀ : S.U)
    (hpt : A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * (yc c).1 * κ₀.1))
    (z z₁ z₂ : Frames (gramC J emb)) (h1 : IsTr (atInf emb (A.gamI i γ)) z₁ z) (h2 : IsTr (atInf emb γ₀) z₂ z₁) :
    (S.chi κ : ℂ) * evC G.P A.rk pos (gramC J emb) (crdB emb A.B)
        (MvPolynomial.map embLL (K.val x i ((G.lev i).smul γ L))) z =
      evC G.P A.rk pos (gramC J emb) (crdB emb A.B)
        (MvPolynomial.map embLL (natActR G.P LL (blkLL A σ tE pos (A.gamI i γ)) (K.val x i L))) z := by
  rw [evC_blk A tE pos emb embLL htE (A.gamI i γ) (unit_of_std A.B _ hBs hγ) (gramC J emb) z₁ z h1,
    K.val_emb x i L g hL c γ₀ hγ₀ κ₀ hpt z₁ z₂ h2]
  have hL' : ∀ v, (G.lev i).smul γ L v = colSpan (G.P.W v)
      (((G.lev i).act v γ * g v : GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
        Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := by
    intro v
    show (L v).map _ = _
    rw [hL v, colSpan_map]
    rfl
  have hpt' : A.IsPt i (fun v => (G.lev i).act v γ * g v)
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ * γ₀) * (yc c).1 * (κ₀ * κ⁻¹ : S.U).1) := by
    have := A.isPt_smul hA i g _ κ.1 hpt γ hκ
    have e1 : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ * γ₀) * (yc c).1 * (κ₀ * κ⁻¹ : S.U).1 =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) *
          (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * (yc c).1 * κ₀.1) * (κ.1)⁻¹ := by
      rw [map_mul]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
    rw [e1]
    exact this
  have h3 : IsTr (atInf emb ((A.gamI i γ * γ₀ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) z₂ z := by
    intro τ
    rw [h1 τ, h2 τ, ← Matrix.mul_assoc, Units.val_mul, atInf_mul]
  rw [K.val_emb x i _ _ hL' c (A.gamI i γ * γ₀) (Subgroup.mul_mem _ hγ hγ₀) (κ₀ * κ⁻¹) hpt' z z₂ h3, ← mul_assoc]
  congr 1
  rw [← Units.val_mul, ← map_mul]
  simp

end Formalism.L2.G.Cmp

end
