import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol

noncomputable section

namespace Formalism.L2.SG.LocVolKap

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Sc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem sc_mul (a b : Fv F v) : sc (E := E) v (a * b) = sc (E := E) v a * sc (E := E) v b := by
  simp only [sc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem sc_one : sc (E := E) v (1 : Fv F v) = 1 := (Algebra.TensorProduct.one_def).symm

theorem sc_natCast (m : ℕ) : sc (E := E) v (m : Fv F v) = (m : Fv F v ⊗[F] E) := by
  induction m with
  | zero => simp [sc]
  | succ k ih =>
    rw [Nat.cast_succ, Nat.cast_succ, ← ih]
    simp only [sc, TensorProduct.add_tmul, Algebra.TensorProduct.one_def]

theorem smul_eq_sc {n : ℕ} (c : v.adicCompletionIntegers F) (y : Fin n → Fv F v ⊗[F] E) :
    c • y = sc (E := E) v (c : Fv F v) • y := by
  funext i
  show (c : Fv F v) • y i = ((c : Fv F v) ⊗ₜ[F] (1 : E)) * y i
  rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem sc_smul_mem {n : ℕ} (Λ : Set (Fin n → E)) (d : Fv F v) (hd : d ∈ v.adicCompletionIntegers F)
    (y : Fin n → Fv F v ⊗[F] E) (hy : y ∈ latLoc (E := E) v Λ) :
    sc (E := E) v d • y ∈ latLoc (E := E) v Λ := by
  have h := Submodule.smul_mem (latLoc (E := E) v Λ) (⟨d, hd⟩ : v.adicCompletionIntegers F) hy
  rwa [smul_eq_sc] at h

theorem natCast_not_mem (c g : ℕ) (hcg : Nat.Coprime c g) (hg : (g : 𝓞 F) ∈ v.asIdeal) :
    (c : 𝓞 F) ∉ v.asIdeal := by
  intro hc
  have hz := Nat.gcd_eq_gcd_ab c g
  rw [Nat.Coprime.gcd_eq_one hcg] at hz
  have key := congrArg (Int.cast : ℤ → 𝓞 F) hz
  push_cast at key
  have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [key]
    exact add_mem (Ideal.mul_mem_right _ _ hc) (Ideal.mul_mem_right _ _ hg)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem inv_natCast_mem (c : ℕ) (hc : (c : 𝓞 F) ∉ v.asIdeal) :
    (c : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F ∧ (c : Fv F v) ≠ 0 := by
  have hv : Valued.v (c : Fv F v) = 1 := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (c : 𝓞 F)
    rw [HeightOneSpectrum.valuation_of_algebraMap] at h
    have h1 : v.intValuation (c : 𝓞 F) = 1 :=
      le_antisymm (v.intValuation_le_one _)
        (not_lt.mp fun h' => hc ((v.intValuation_lt_one_iff_mem _).mp h'))
    rw [h1] at h
    simpa using h
  refine ⟨?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
  · intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv

theorem natCast_mem_int (k : ℕ) : (k : Fv F v) ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ]
    exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

end Sc

section Comp

variable (I : Formalism.MainNotions.S.AutInst) (v : HeightOneSpectrum (𝓞 I.F))

def rhoE : I.E ⊗[I.F] Af I.F →+* Fv I.F v ⊗[I.F] I.E :=
  ((Algebra.TensorProduct.map (evalV I.F v) (AlgHom.id I.F I.E)).comp
    (Algebra.TensorProduct.comm I.F I.E (Af I.F)).toAlgHom).toRingHom

theorem rhoE_tmul (x : I.E) (a : Af I.F) : rhoE I v (x ⊗ₜ[I.F] a) = evalV I.F v a ⊗ₜ[I.F] x := by
  simp [rhoE]

theorem rhoE_inclE (x : I.E) : rhoE I v (Formalism.UG.inclE (F := I.F) (Af I.F) x) = inclR (Fv I.F v) x := by
  show rhoE I v (x ⊗ₜ[I.F] (1 : Af I.F)) = (1 : Fv I.F v) ⊗ₜ[I.F] x
  rw [rhoE_tmul, map_one]

theorem rhoE_sig : (rhoE I v).comp (Formalism.UG.sigR I.cm.sig (Af I.F)) =
    (sigR (Fv I.F v) I.cm.sig).comp (rhoE I v) := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [RingHom.comp_apply]
    rw [show Formalism.UG.sigR I.cm.sig (Af I.F) (a ⊗ₜ[I.F] b) = I.cm.sig a ⊗ₜ[I.F] b by
      simp [Formalism.UG.sigR], rhoE_tmul, rhoE_tmul]
    simp [sigR]
  | add x y hx hy =>
    simp only [RingHom.comp_apply, map_add] at *
    rw [hx, hy]

theorem bc_rhoE_mem (x : I.Gf) :
    Formalism.UG.bc (rhoE I v) (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ HR (Fv I.F v) I.cm.sig I.J := by
  have h := Formalism.UG.P.bc_mem (Formalism.UG.sigR I.cm.sig (Af I.F)) (sigR (Fv I.F v) I.cm.sig) (rhoE I v)
    (rhoE_sig I v) (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) x (by exact x.2)
  have hJ : (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).map (rhoE I v) = JR (Fv I.F v) I.J := by
    ext i j
    simp [JR, rhoE_inclE]
  rw [hJ] at h
  exact h

def kap (x : I.Gf) : HA (Fv I.F v) I.cm.sig I.J :=
  (⟨Formalism.UG.bc (rhoE I v) (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)), bc_rhoE_mem I v x⟩ :
    HR (Fv I.F v) I.cm.sig I.J)

def rhoV (w : Fin I.n → I.E ⊗[I.F] Af I.F) : Fin I.n → Fv I.F v ⊗[I.F] I.E := fun i => rhoE I v (w i)

theorem rhoV_incl (y : Fin I.n → I.E) : rhoV I v (incl I y) = ratV (F := I.F) (Fv I.F v) y := by
  funext i
  exact rhoE_inclE I v (y i)

theorem rhoV_sub (a b : Fin I.n → I.E ⊗[I.F] Af I.F) : rhoV I v (a - b) = rhoV I v a - rhoV I v b := by
  funext i
  simp [rhoV]

theorem rhoV_smul (t : I.E ⊗[I.F] Af I.F) (a : Fin I.n → I.E ⊗[I.F] Af I.F) :
    rhoV I v (t • a) = rhoE I v t • rhoV I v a := by
  funext i
  simp [rhoV]

theorem map_mulVec_rhoV (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (w : Fin I.n → I.E ⊗[I.F] Af I.F) :
    (M.map (rhoE I v)) *ᵥ rhoV I v w = rhoV I v (M *ᵥ w) := by
  funext i
  simp only [rhoV]
  rw [RingHom.map_mulVec]
  rfl

theorem kap_smul_ratTup {a : ℕ} (x : I.Gf) (Y : Fin a → Fin I.n → I.E) (b : Fin a) :
    ((kap I v x) • ratTup (F := I.F) (Fv I.F v) Y) b = rhoV I v (I.fmat x *ᵥ incl I (Y b)) := by
  rw [← map_mulVec_rhoV, rhoV_incl]
  rfl

theorem ratTup_eq {a : ℕ} (Y : Fin a → Fin I.n → I.E) (b : Fin a) :
    ratTup (F := I.F) (Fv I.F v) Y b = rhoV I v (incl I (Y b)) := by
  rw [rhoV_incl]
  rfl

theorem fmat_mul (x y : I.Gf) : I.fmat (x * y) = I.fmat x * I.fmat y := by
  simp [Formalism.MainNotions.S.AutInst.fmat]

theorem fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  simp [Formalism.MainNotions.S.AutInst.fmat]

theorem fmat_mul_inv (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  simp [Formalism.MainNotions.S.AutInst.fmat]

end Comp

section Lat

variable (I : Formalism.MainNotions.S.AutInst) (v : HeightOneSpectrum (𝓞 I.F))

theorem inclR_smul_mem (o : 𝓞 I.E) (y : Fin I.n → Fv I.F v ⊗[I.F] I.E)
    (hy : y ∈ latLoc (E := I.E) v (I.L : Set (Fin I.n → I.E))) :
    inclR (F := I.F) (Fv I.F v) (o : I.E) • y ∈ latLoc (E := I.E) v (I.L : Set (Fin I.n → I.E)) := by
  have hy' : y ∈ Submodule.span (v.adicCompletionIntegers I.F)
      (ratV (F := I.F) (Fv I.F v) '' (I.L : Set (Fin I.n → I.E))) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, hl, rfl⟩ := hz
    have hol : o • l ∈ I.L := I.L.smul_mem o hl
    have e : inclR (F := I.F) (Fv I.F v) (o : I.E) • ratV (F := I.F) (Fv I.F v) l = ratV (F := I.F) (Fv I.F v) (o • l) := by
      funext i
      show inclR (F := I.F) (Fv I.F v) (o : I.E) * inclR (F := I.F) (Fv I.F v) (l i) = inclR (F := I.F) (Fv I.F v) (o • l i)
      rw [← map_mul, Algebra.smul_def (R := 𝓞 I.E)]
    rw [e]
    exact Submodule.subset_span ⟨_, hol, rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [smul_add]
    exact add_mem ha hb
  | smul c a _ ha =>
    rw [smul_eq_sc, smul_smul, mul_comm, ← smul_smul, ← smul_eq_sc]
    exact Submodule.smul_mem _ c ha

theorem rhoE_int (t : I.E ⊗[I.F] Af I.F) (ht : t ∈ Formalism.MainNotions.S.IntAf I.F I.E) :
    ∀ y ∈ latLoc (E := I.E) v (I.L : Set (Fin I.n → I.E)),
      rhoE I v t • y ∈ latLoc (E := I.E) v (I.L : Set (Fin I.n → I.E)) := by
  have ht' : t ∈ Subring.closure (Set.range (fun x : Formalism.UG.intOE I.E => (x : I.E) ⊗ₜ[I.F] (1 : Af I.F)) ∪
      Set.range (fun y : Formalism.UG.intAd I.F => (1 : I.E) ⊗ₜ[I.F] (y : Af I.F))) := ht
  clear ht
  induction ht' using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨o, ho⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩
    · obtain ⟨o', rfl⟩ := ho
      intro y hy
      have e : rhoE I v (((algebraMap (𝓞 I.E) I.E) o') ⊗ₜ[I.F] (1 : Af I.F)) = inclR (F := I.F) (Fv I.F v) (o' : I.E) := by
        rw [rhoE_tmul, map_one]
        rfl
      rw [e]
      exact inclR_smul_mem I v o' y hy
    · intro y hy
      rw [rhoE_tmul]
      exact sc_smul_mem v _ (evalV I.F v a) (ha v) y hy
  | zero =>
    intro y _
    simp
  | one =>
    intro y hy
    simpa using hy
  | add x z _ _ hx hz =>
    intro y hy
    rw [map_add, add_smul]
    exact add_mem (hx y hy) (hz y hy)
  | neg x _ hx =>
    intro y hy
    rw [map_neg, neg_smul]
    exact neg_mem (hx y hy)
  | mul x z _ _ hx hz =>
    intro y hy
    rw [map_mul, mul_smul]
    exact hx _ (hz y hy)

theorem incl_mem_Lf (l : Fin I.n → I.E) (hl : l ∈ I.L) : incl I l ∈ I.Lf :=
  Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩

theorem rhoV_Lf (w : Fin I.n → I.E ⊗[I.F] Af I.F) (hw : w ∈ I.Lf) :
    rhoV I v w ∈ latLoc (E := I.E) v (I.L : Set (Fin I.n → I.E)) := by
  have hw' : w ∈ Submodule.span (Formalism.MainNotions.S.IntAf I.F I.E)
      (Set.range fun x : I.L => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((x : Fin I.n → I.E) i)) := hw
  clear hw
  induction hw' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hz
    rw [show rhoV I v (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) = ratV (F := I.F) (Fv I.F v) l
      from rhoV_incl I v l]
    exact Submodule.subset_span ⟨l, hl, rfl⟩
  | zero =>
    have e : rhoV I v 0 = 0 := by
      funext i
      simp [rhoV]
    rw [e]
    exact zero_mem _
  | add a b _ _ ha hb =>
    have e : rhoV I v (a + b) = rhoV I v a + rhoV I v b := by
      funext i
      simp [rhoV]
    rw [e]
    exact add_mem ha hb
  | smul t a _ ha =>
    have e : rhoV I v (t • a) = rhoE I v (t : I.E ⊗[I.F] Af I.F) • rhoV I v a := by
      funext i
      show rhoE I v ((t : I.E ⊗[I.F] Af I.F) * a i) = rhoE I v t * rhoE I v (a i)
      exact map_mul _ _ _
    rw [e]
    exact rhoE_int I v t t.2 _ ha

end Lat

section Lat2

variable (I : Formalism.MainNotions.S.AutInst) (v : HeightOneSpectrum (𝓞 I.F))

theorem rhoV_mL (m : ℕ) (w : Fin I.n → I.E ⊗[I.F] Af I.F) (hw : w ∈ mL I m) :
    ∃ y ∈ latLoc (E := I.E) v (I.L : Set (Fin I.n → I.E)), rhoV I v w = sc (E := I.E) v (m : Fv I.F v) • y := by
  have hw' : w ∈ Submodule.span (Formalism.MainNotions.S.IntAf I.F I.E)
      {y | ∃ x ∈ I.Lf, y = (m : I.E ⊗[I.F] Af I.F) • x} := hw
  clear hw
  induction hw' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨rhoV I v x, rhoV_Lf I v x hx, ?_⟩
    rw [rhoV_smul, map_natCast, sc_natCast]
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    rw [smul_zero]
    funext i
    simp [rhoV]
  | add a b _ _ ha hb =>
    obtain ⟨ya, hya, ea⟩ := ha
    obtain ⟨yb, hyb, eb⟩ := hb
    refine ⟨ya + yb, add_mem hya hyb, ?_⟩
    rw [smul_add, ← ea, ← eb]
    funext i
    simp [rhoV]
  | smul t a _ ha =>
    obtain ⟨ya, hya, ea⟩ := ha
    refine ⟨rhoE I v (t : I.E ⊗[I.F] Af I.F) • ya, rhoE_int I v t t.2 ya hya, ?_⟩
    have e : rhoV I v (t • a) = rhoE I v (t : I.E ⊗[I.F] Af I.F) • rhoV I v a := by
      funext i
      show rhoE I v ((t : I.E ⊗[I.F] Af I.F) * a i) = rhoE I v t * rhoE I v (a i)
      exact map_mul _ _ _
    rw [e, ea, smul_smul, smul_smul, mul_comm]

theorem natCast_smul_mL (m c : ℕ) (w : Fin I.n → I.E ⊗[I.F] Af I.F) (hw : w ∈ mL I m) :
    (c : I.E ⊗[I.F] Af I.F) • w ∈ mL I m := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hw c

theorem kset_inv (x : I.Gf) (hx : x ∈ I.Kset) : x⁻¹ ∈ I.Kset := by
  show ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [Subgroup.coe_inv]
  exact (Formalism.UG.stabGL I.Lf).inv_mem hx

theorem kset_mul (x y : I.Gf) (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) : x * y ∈ I.Kset := by
  show ((x * y : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [Subgroup.coe_mul]
  exact (Formalism.UG.stabGL I.Lf).mul_mem hx hy

theorem kap_fwd (x : I.Gf) (hx : x ∈ I.Kset) (y : Fin I.n → Fv I.F v ⊗[I.F] I.E)
    (hy : y ∈ latLoc (E := I.E) v (I.L : Set (Fin I.n → I.E))) :
    (I.fmat x).map (rhoE I v) *ᵥ y ∈ latLoc (E := I.E) v (I.L : Set (Fin I.n → I.E)) := by
  have hy' : y ∈ Submodule.span (v.adicCompletionIntegers I.F)
      (ratV (F := I.F) (Fv I.F v) '' (I.L : Set (Fin I.n → I.E))) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, hl, rfl⟩ := hz
    rw [← rhoV_incl, map_mulVec_rhoV]
    exact rhoV_Lf I v _ ((hx (incl I l)).mp (incl_mem_Lf I l hl))
  | zero =>
    rw [Matrix.mulVec_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    rw [Matrix.mulVec_add]
    exact add_mem ha hb
  | smul c a _ ha =>
    rw [smul_eq_sc, Matrix.mulVec_smul, ← smul_eq_sc]
    exact Submodule.smul_mem _ c ha

theorem kap_K (x : I.Gf) (hx : x ∈ I.Kset) :
    kap I v x ∈ Kv I.cm.sig I.J (I.L : Set (Fin I.n → I.E)) v := by
  show ∀ y, y ∈ latLoc (E := I.E) v (I.L : Set (Fin I.n → I.E)) ↔
    (I.fmat x).map (rhoE I v) *ᵥ y ∈ latLoc (E := I.E) v (I.L : Set (Fin I.n → I.E))
  intro y
  refine ⟨kap_fwd I v x hx y, fun h => ?_⟩
  have h2 := kap_fwd I v x⁻¹ (kset_inv I x hx) _ h
  rwa [Matrix.mulVec_mulVec, ← Matrix.map_mul, fmat_inv_mul,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at h2

end Lat2

section Main

open Formalism.BasicNotions

variable {D : D7} (X : HidaSetting D)

theorem typed_mem (p : TypX X) :
    ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
  have h := p.2
  unfold typSet at h
  split_ifs at h with hf
  · exact (Set.Finite.mem_toFinset hf).mp h
  · simp at h

theorem Bg_mem (p : TypX X) : ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
  rw [X.g_eq, Nat.cast_mul]
  rcases typed_mem X p with h | h
  · exact Ideal.mul_mem_right _ _ h
  · exact Ideal.mul_mem_left _ _ h

theorem gAt_dvd (v : PlX X) : ∃ k : ℕ, X.B.g = gAt X v * k := by
  unfold gAt
  split_ifs
  · exact ⟨D.host.g 1, X.g_eq⟩
  · exact ⟨D.host.g 0, by rw [X.g_eq, mul_comm]⟩

theorem alp_last (v : PlX X) (r : ℕ) : alp v r (Fin.last r) = 1 := by
  simp [alp]

theorem locF_last {v : PlX X} {r : ℕ} (Y : TupV (E := X.B.I.E) v X.B.I.n (r + 1)) :
    locF v Y (Fin.last r) = Y (Fin.last r) := by
  rw [locF, alp_last, sc_one, one_smul]

theorem glob_diff {R : Type} [CommRing R] {n : ℕ} (A Ai A'i : Matrix (Fin n) (Fin n) R) (h : A * Ai = 1)
    (z z' z0 : Fin n → R) :
    (A * A'i) *ᵥ z' - z = A *ᵥ ((A'i *ᵥ z' - z0) - (Ai *ᵥ z - z0)) := by
  simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  abel

theorem kapX (_hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (u u' : D.what₂.Word) : KapX X u u' := by
  intro p
  refine ⟨kap X.B.I p.1 (X.xu u * (X.xu u')⁻¹),
    kap_K X.B.I p.1 _ (kset_mul X.B.I _ _ (X.xu_K u) (kset_inv X.B.I _ (X.xu_K u'))), ?_⟩
  intro a
  induction a using Fin.lastCases with
  | cast b =>
    refine ⟨0, zero_mem _, ?_⟩
    have hfix : X.B.I.fmat (X.xu u * (X.xu u')⁻¹) *ᵥ incl X.B.I (crdOf X.B.I X.ιE X.bas (X.eX b)) =
        incl X.B.I (crdOf X.B.I X.ιE X.bas (X.eX b)) := by
      have h1 : X.B.I.fmat (X.xu u')⁻¹ *ᵥ incl X.B.I (crdOf X.B.I X.ιE X.bas (X.eX b)) =
          incl X.B.I (crdOf X.B.I X.ιE X.bas (X.eX b)) := by
        conv_lhs => rw [← (X.xu_fix u' b).1]
        rw [Matrix.mulVec_mulVec, fmat_inv_mul, Matrix.one_mulVec]
      rw [fmat_mul, ← Matrix.mulVec_mulVec, h1, (X.xu_fix u b).1]
    have heq : (kap X.B.I p.1 (X.xu u * (X.xu u')⁻¹) • ratTup (F := X.B.I.F) (Fv X.B.I.F p.1) (F0 (frameOf X u')))
        (Fin.castSucc b) = ratTup (F := X.B.I.F) (Fv X.B.I.F p.1) (F0 (frameOf X u)) (Fin.castSucc b) := by
      rw [kap_smul_ratTup, ratTup_eq]
      simp only [F0, frameOf, Fin.snoc_castSucc]
      rw [hfix]
    simp only [locF, heq, sub_self, smul_zero]
  | last =>
    obtain ⟨c1, hc1, hm1⟩ := X.xu_z u
    obtain ⟨c2, hc2, hm2⟩ := X.xu_z u'
    have hm : ((c1 * c2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
        ((X.B.I.fmat (X.xu u')⁻¹ *ᵥ incl X.B.I (crdOf X.B.I X.ιE X.bas (X.zu u')) - X.z0) -
          (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (crdOf X.B.I X.ιE X.bas (X.zu u)) - X.z0)) ∈
        mL X.B.I X.B.g := by
      have h := sub_mem (natCast_smul_mL X.B.I _ c1 _ hm2) (natCast_smul_mL X.B.I _ c2 _ hm1)
      convert h using 1
      rw [smul_sub, Nat.cast_mul, mul_smul, mul_comm (c1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), mul_smul]
    obtain ⟨y0, hy0, hy0e⟩ := rhoV_mL X.B.I p.1 _ _ hm
    have hy1 := kap_fwd X.B.I p.1 _ (X.xu_K u) y0 hy0
    have hc : ((c1 * c2 : ℕ) : 𝓞 X.B.I.F) ∉ p.1.asIdeal :=
      natCast_not_mem p.1 _ X.B.g (Nat.Coprime.mul_left hc1 hc2) (Bg_mem X p)
    obtain ⟨hdi, hc0⟩ := inv_natCast_mem p.1 _ hc
    obtain ⟨k, hk⟩ := gAt_dvd X p.1
    refine ⟨sc (E := X.B.I.E) p.1 (k : Fv X.B.I.F p.1) • sc (E := X.B.I.E) p.1 ((c1 * c2 : ℕ) : Fv X.B.I.F p.1)⁻¹ •
      ((X.B.I.fmat (X.xu u)).map (rhoE X.B.I p.1) *ᵥ y0),
      sc_smul_mem p.1 _ _ (natCast_mem_int p.1 k) _ (sc_smul_mem p.1 _ _ hdi _ hy1), ?_⟩
    rw [locF_last, locF_last, kap_smul_ratTup, ratTup_eq, ← rhoV_sub]
    simp only [F0, frameOf, Fin.snoc_last]
    rw [fmat_mul, glob_diff _ _ _ (fmat_mul_inv X.B.I (X.xu u)) _ _ X.z0]
    have key : sc (E := X.B.I.E) p.1 ((c1 * c2 : ℕ) : Fv X.B.I.F p.1) •
        rhoV X.B.I p.1 (X.B.I.fmat (X.xu u) *ᵥ
          ((X.B.I.fmat (X.xu u')⁻¹ *ᵥ incl X.B.I (crdOf X.B.I X.ιE X.bas (X.zu u')) - X.z0) -
            (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (crdOf X.B.I X.ιE X.bas (X.zu u)) - X.z0))) =
        sc (E := X.B.I.E) p.1 (X.B.g : Fv X.B.I.F p.1) • ((X.B.I.fmat (X.xu u)).map (rhoE X.B.I p.1) *ᵥ y0) := by
      rw [sc_natCast, ← map_natCast (rhoE X.B.I p.1), ← rhoV_smul, ← Matrix.mulVec_smul,
        ← map_mulVec_rhoV, hy0e, Matrix.mulVec_smul]
    have hcc : sc (E := X.B.I.E) p.1 ((c1 * c2 : ℕ) : Fv X.B.I.F p.1)⁻¹ *
        sc (E := X.B.I.E) p.1 ((c1 * c2 : ℕ) : Fv X.B.I.F p.1) = 1 := by
      rw [← sc_mul, inv_mul_cancel₀ hc0, sc_one]
    rw [← one_smul (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) (rhoV X.B.I p.1 _), ← hcc, mul_smul, key]
    simp only [smul_smul]
    congr 1
    rw [hk, Nat.cast_mul (gAt X p.1) k, sc_mul]
    ring

end Main

end Formalism.L2.SG.LocVolKap
