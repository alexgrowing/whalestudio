import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.FockRSmulLeft
import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.MainNotions.G

variable {O K Kc : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [CharZero K] [Field Kc] [Algebra K Kc]
  {B τ : Type} [Fintype B] [DecidableEq B] {n : ℕ} (em : B → Fin n × Fin n → τ)
  (hem : Function.Injective fun x : B × (Fin n × Fin n) => em x.1 x.2)
  (ν : B → Fin n → ℕ) (hν : ∀ b, Antitone (ν b))
  (h hi : B → Matrix (Fin n) (Fin n) K) (hh : ∀ b, hi b * h b = 1)
  (M : AddSubgroup Kc) (hM : ∀ (o : O), ∀ a ∈ M, algebraMap K Kc (algebraMap O K o) * a ∈ M)

theorem toK_bidet {r n K' : ℕ} (sz : Fin K' → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    toK O K (bideterminant O sz hsz I) = bideterminant K sz hsz I := by
  show map (algebraMap O K) _ = _
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

include hem hν hh hM in

theorem tgt_bidet (hDB : DualBases) (hFP : FockProd) (hRe : Reorder) (c : B → ℕ) (sz : ∀ b, Fin (c b) → ℕ)
    (hsz : ∀ b k, sz b k ≤ n) (hshape : ∀ b, shapeDeg (sz b) = ν b) (y : MvPolynomial τ Kc)
    (hy : y ∈ Submodule.span Kc {z | ∃ F : B → MvPolynomial (Fin n × Fin n) K, (∀ b, F b ∈ dualWeyl K n n (ν b)) ∧
      z = map (algebraMap K Kc) (∏ b, rename (em b) (F b))})
    (hp : ∀ I : ∀ b, ∀ k, Fin (sz b k) → Fin n,
      ∃ a ∈ M, fockR y (map (algebraMap K Kc) (∏ b, rename (em b) (rowAct K (h b).transpose (bideterminant K (sz b) (hsz b) (I b))))) =
        a * ∏ b, cN Kc (ν b)) :
    y ∈ AddSubgroup.closure {z | ∃ a ∈ M, ∃ F : B → MvPolynomial (Fin n × Fin n) K,
      (∀ b, F b ∈ deltaL O K n (ν b) (h b)) ∧ z = a • map (algebraMap K Kc) (∏ b, rename (em b) (F b))} := by
  refine tgt_abs (O := O) em hem ν hν h hi hh M hDB hFP y hy fun Q hQ => ?_
  let T : Submodule O (MvPolynomial τ K) :=
    { carrier := {Z | ∃ a ∈ M, fockR y (map (algebraMap K Kc) Z) = a * ∏ b, cN Kc (ν b)}
      add_mem' := by
        rintro Z Z' ⟨a, ha, h1⟩ ⟨a', ha', h2⟩
        refine ⟨a + a', M.add_mem ha ha', ?_⟩
        rw [map_add, fockR_comm, fockR_add_left, fockR_comm _ y, fockR_comm _ y, h1, h2, add_mul]
      zero_mem' := ⟨0, M.zero_mem, by rw [map_zero, fockR_comm, fockR_zero_left, zero_mul]⟩
      smul_mem' := by
        rintro o Z ⟨a, ha, h1⟩
        refine ⟨_, hM o a ha, ?_⟩
        rw [← algebraMap_smul K o Z, smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul, fockR_comm, fockR_smul_left, fockR_comm, h1,
          mul_assoc] }
  refine prod_span (R := O) (fun b => Set.range fun I : ∀ k, Fin (sz b k) → Fin n =>
    rename (em b) (rowAct K (h b).transpose (bideterminant K (sz b) (hsz b) I))) T ?_ _ ?_
  · intro f hf
    choose I hI using hf
    obtain ⟨a, ha, h1⟩ := hp I
    refine ⟨a, ha, ?_⟩
    rw [← Finset.prod_congr rfl fun b _ => hI b]
    exact h1
  · intro b
    have h1 := hQ b
    rw [standardMonomialSpanDomain O n n (ν b), Submodule.map_span] at h1
    have h2 := Submodule.mem_map_of_mem (f := (((rename (em b) : MvPolynomial (Fin n × Fin n) K →ₐ[K] MvPolynomial τ K).comp
      (rowAct K (h b).transpose)).toLinearMap).restrictScalars O) h1
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨_, ⟨K', sz', hsz', I', hs', rfl⟩, rfl⟩, rfl⟩
    obtain ⟨I'', hI''⟩ := hRe K n n K' (c b) sz' (sz b) hsz' (hsz b) (hs'.trans (hshape b).symm) I'
    refine ⟨I'', ?_⟩
    rw [toK_bidet, hI'']
    rfl

end Formalism.L2.PairingIndexBounds.Ent
