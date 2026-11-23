import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.LatSOfLocBasis
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.G.Cmp
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

section Split

variable (v : HeightOneSpectrum (𝓞 F))
  (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
  (halg : ∀ a : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a))

abbrev piF : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F := (RingHom.fst _ _).comp φ.toRingHom

abbrev piE : E →+* v.adicCompletion F := (piF v φ).comp (inclE (F := F) (v.adicCompletion F))

theorem single_intO (j a : Fin n) : (Pi.single j 1 : Fin n → v.adicCompletion F) a ∈ v.adicCompletionIntegers F := by
  by_cases h : a = j
  · subst h; rw [Pi.single_eq_same]; exact one_mem _
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem fst_mulVec' (M : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (x : Fin n → E ⊗[F] v.adicCompletion F) :
    (fun a => (φ (((M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ x) a)).1) =
      ((bc (piF v φ) M : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ
        (fun a => (φ (x a)).1) := by
  funext a
  exact RingHom.map_mulVec (piF v φ) _ _ _

include halg in

theorem fst_latB (B' : GL (Fin n) E) (t : Fin n → v.adicCompletion F) :
    (∃ x ∈ Formalism.L2.Herm.locL v (latB B'), ∀ a, (φ (x a)).1 = t a) ↔
      ∀ a, (((bc (piE v φ) B')⁻¹ : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec t a ∈ v.adicCompletionIntegers F :=
  Formalism.MainNotions.Gaps.Loc.fr_lat_of v φ halg (latB B') B' (fun x hx => hx) 1
    (by rw [Nat.cast_one]; exact v.asIdeal.ne_top_iff_one.1 v.isPrime.ne_top)
    (fun i => by rw [Nat.cast_one, one_smul]; exact latB_col B' i) t

include halg in

theorem int_of_move {Lb : Submodule (𝓞 E) (Fin n → E)} (B B' : GL (Fin n) E)
    (hb : ∀ t : Fin n → v.adicCompletion F, (∃ x ∈ Formalism.L2.Herm.locL v Lb, ∀ a, (φ (x a)).1 = t a) ↔
      ∀ a, (((bc (piE v φ) B)⁻¹ : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec t a ∈ v.adicCompletionIntegers F)
    (u : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hu : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (latB B') ↔
      ((u⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ x ∈
        latS (F := F) (v.adicCompletion F) (intV E v) Lb) :
    (∀ a b, (((bc (piE v φ) B')⁻¹ * bc (piF v φ) u * bc (piE v φ) B : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b ∈ v.adicCompletionIntegers F) ∧
    (∀ a b, (((bc (piE v φ) B)⁻¹ * (bc (piF v φ) u)⁻¹ * bc (piE v φ) B' : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b ∈ v.adicCompletionIntegers F) := by
  constructor
  · intro a b
    obtain ⟨x, hx, hxt⟩ := (hb (((bc (piE v φ) B : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ Pi.single b 1)).2 (fun a => by
        show ((((bc (piE v φ) B)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ
          (((bc (piE v φ) B : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ
            Pi.single b 1)) a ∈ _
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
        exact single_intO v b a)
    have hx' : (u : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ x ∈
        latS (F := F) (v.adicCompletion F) (intV E v) (latB B') := by
      refine (hu _).2 ?_
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact hx
    have h3 := (fst_latB v φ halg B' _).1 ⟨_, hx', fun a => rfl⟩ a
    rw [fst_mulVec', (funext hxt : (fun a => (φ (x a)).1) = _)] at h3
    rw [entry_eq (((bc (piE v φ) B')⁻¹ * bc (piF v φ) u * bc (piE v φ) B : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h3
  · intro a b
    obtain ⟨x, hx, hxt⟩ := (fst_latB v φ halg B' (((bc (piE v φ) B' : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ Pi.single b 1)).2 (fun a => by
        show ((((bc (piE v φ) B')⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ
          (((bc (piE v φ) B' : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ
            Pi.single b 1)) a ∈ _
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
        exact single_intO v b a)
    have hx' := (hu x).1 hx
    have h3 := (hb _).1 ⟨_, hx', fun a => rfl⟩ a
    rw [fst_mulVec', (funext hxt : (fun a => (φ (x a)).1) = _), map_inv] at h3
    rw [entry_eq (((bc (piE v φ) B)⁻¹ * (bc (piF v φ) u)⁻¹ * bc (piE v φ) B' : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h3

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

theorem gram_entry (B' : GL (Fin n) E) (a b : Fin n) :
    (cT (σ : E →+* E) (B' : Matrix (Fin n) (Fin n) E) * J * (B' : Matrix (Fin n) (Fin n) E)) a b =
      hform (σ : E →+* E) J ((B' : Matrix (Fin n) (Fin n) E) *ᵥ Pi.single a 1) ((B' : Matrix (Fin n) (Fin n) E) *ᵥ Pi.single b 1) := by
  rw [Formalism.UG.P.hform_mulVec, Formalism.UG.P.hform_single]

variable {σ J}

theorem gram_intV (B' : GL (Fin n) E) (hsd : SelfDualAt σ J v (latB B')) (a b : Fin n) :
    inclE (F := F) (v.adicCompletion F)
      ((cT (σ : E →+* E) (B' : Matrix (Fin n) (Fin n) E) * J * (B' : Matrix (Fin n) (Fin n) E)) a b) ∈ intV E v := by
  rw [gram_entry, ← hform_incl]
  exact (hsd _).1 (Submodule.subset_span ⟨_, latB_col B' b, rfl⟩) _ (Submodule.subset_span ⟨_, latB_col B' a, rfl⟩)

theorem gramInv_intV (B' : GL (Fin n) E) (hsd : SelfDualAt σ J v (latB B'))
    (hG : IsUnit (cT (σ : E →+* E) (B' : Matrix (Fin n) (Fin n) E) * J * (B' : Matrix (Fin n) (Fin n) E)).det) (a b : Fin n) :
    inclE (F := F) (v.adicCompletion F)
      ((cT (σ : E →+* E) (B' : Matrix (Fin n) (Fin n) E) * J * (B' : Matrix (Fin n) (Fin n) E))⁻¹ a b) ∈ intV E v := by
  set Gm := cT (σ : E →+* E) (B' : Matrix (Fin n) (Fin n) E) * J * (B' : Matrix (Fin n) (Fin n) E) with hGm
  have hdual : (B' : Matrix (Fin n) (Fin n) E) *ᵥ (Gm⁻¹ *ᵥ Pi.single b 1) ∈ dualSet (σ : E →+* E) J (latB B') := by
    intro x hx
    have hxB : x = (B' : Matrix (Fin n) (Fin n) E) *ᵥ (((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [hxB, Formalism.UG.P.hform_mulVec, ← hGm, Formalism.UG.P.hform_eq_dot, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG,
      Matrix.one_mulVec, dotProduct_single, mul_one]
    obtain ⟨c, hc⟩ := hx b
    show σ ((((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x) b) ∈ _
    rw [← hc]
    exact sig_int σ c
  have hmem := (hsd _).2 fun z hz => pair_int v σ J (latB B') _ hdual z hz
  have h1 := (mem_latS_latB v B' _).1 hmem a
  rw [← map_inv] at h1
  have e := incl_mulVec v ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
    ((B' : Matrix (Fin n) (Fin n) E) *ᵥ (Gm⁻¹ *ᵥ Pi.single b 1))
  have e' : ((bc (inclE (F := F) (v.adicCompletion F)) B'⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ (fun i => inclE (F := F) (v.adicCompletion F)
        (((B' : Matrix (Fin n) (Fin n) E) *ᵥ (Gm⁻¹ *ᵥ Pi.single b 1)) i)) = _ := e
  rw [e'] at h1
  rw [entry_eq Gm⁻¹ a b]
  have e2 : ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ((B' : Matrix (Fin n) (Fin n) E) *ᵥ (Gm⁻¹ *ᵥ Pi.single b 1)) =
      Gm⁻¹ *ᵥ Pi.single b 1 := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [e2] at h1
  exact h1

end Split

section Pt

variable {p : ℕ} {G : GAtP p} (A : LocAt F E n G)

theorem int_back (hW : LocInt A) (v : Fin G.P.nV) (h : GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hh : ∀ a b, (bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) h) :
      Matrix (Fin n) (Fin n) _) a b ∈ (A.pl v).1.adicCompletionIntegers F) (a b : Fin (G.P.m + 1)) :
    (h : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) a b ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
  have h0 := hh (Fin.cast A.rk a) (Fin.cast A.rk b)
  have h1 : (bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) h) : Matrix (Fin n) (Fin n) _)
      (Fin.cast A.rk a) (Fin.cast A.rk b) =
      A.eQ v ((castGL A.rk (G.P.Qq v) h : Matrix (Fin n) (Fin n) _) (Fin.cast A.rk a) (Fin.cast A.rk b)) := rfl
  rw [h1, castGL_apply] at h0
  exact (hW v _).2 h0

theorem bc_eQ_iw (v : Fin G.P.nV) (N : GL (Fin n) E) :
    bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (bc (A.iw v) N) = bc (A.phE v) N := by
  apply Units.ext
  exact Matrix.ext fun a b => (A.eQ v).apply_symm_apply _

theorem bc_ph_incl (v : Fin G.P.nV) (γ : GL (Fin n) E) :
    bc (A.ph v) (bc (prV (E := E) (A.pl v).1) (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ)) = bc (A.phE v) γ := by
  apply Units.ext
  exact Matrix.ext fun a b => rfl

theorem lat_of_int (hW : LocInt A) (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (γ B' : GL (Fin n) E)
    (z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hpt : A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * z)) (v : Fin G.P.nV)
    (h1 : ∀ a b, (((bc (A.phE v) B')⁻¹ * bc (A.ph v) (bc (prV (E := E) (A.pl v).1) z) * bc (A.phE v) A.B :
      GL (Fin n) ((A.pl v).1.adicCompletion F)) : Matrix (Fin n) (Fin n) _) a b ∈ (A.pl v).1.adicCompletionIntegers F)
    (h2 : ∀ a b, (((bc (A.phE v) A.B)⁻¹ * (bc (A.ph v) (bc (prV (E := E) (A.pl v).1) z))⁻¹ * bc (A.phE v) B' :
      GL (Fin n) ((A.pl v).1.adicCompletion F)) : Matrix (Fin n) (Fin n) _) a b ∈ (A.pl v).1.adicCompletionIntegers F) :
    colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) =
      colSpan (G.P.W v) (((castGL A.rk (G.P.Qq v)).symm (bc (A.iw v) (A.B⁻¹ * γ * B')) : GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
        Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := by
  have key : bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v)
      (((castGL A.rk (G.P.Qq v)).symm (bc (A.iw v) (A.B⁻¹ * γ * B')))⁻¹ * g v)) =
      (bc (A.phE v) B')⁻¹ * bc (A.ph v) (bc (prV (E := E) (A.pl v).1) z) * bc (A.phE v) A.B := by
    have h3 := hpt.2 v
    rw [map_mul, map_mul, bc_ph_incl] at h3
    have h4 : bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) (g v)) =
        (bc (A.phE v) A.B)⁻¹ * (bc (A.phE v) γ * bc (A.ph v) (bc (prV (E := E) (A.pl v).1) z)) * bc (A.phE v) A.B := by
      rw [h3]; group
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply, bc_eQ_iw, h4, map_mul, map_mul, map_inv]
    group
  rw [colSpan_eq, colSpan_eq, gMap_std_eq_iff, stabStd_iff]
  constructor
  · refine int_back A hW v _ ?_
    rw [key]
    exact h1
  · refine int_back A hW v _ ?_
    rw [map_inv, map_inv, key]
    have e : ((bc (A.phE v) B')⁻¹ * bc (A.ph v) (bc (prV (E := E) (A.pl v).1) z) * bc (A.phE v) A.B)⁻¹ =
        (bc (A.phE v) A.B)⁻¹ * (bc (A.ph v) (bc (prV (E := E) (A.pl v).1) z))⁻¹ * bc (A.phE v) B' := by group
    rw [e]
    exact h2

end Pt

end Formalism.L2.G.RelativeIndexFlags
