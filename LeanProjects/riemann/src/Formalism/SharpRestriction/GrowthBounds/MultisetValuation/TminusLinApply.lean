import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

section PlacesLevel

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem edges_fin (v : Fin P.nV) (i : ℕ) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    {L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) | IsEdge p (P.n' v) i ⟨L'', L⟩}.Finite := by
  apply Formalism.MainNotions.G.LatticeSystems.ef_edges_finite_gen
  apply Nat.finite_of_card_ne_zero
  rw [(P.setting v).res_card]
  exact pow_ne_zero _ (P.setting v).prime.ne_zero

def EE (v : Fin P.nV) (i : ℕ) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    Finset (Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :=
  (edges_fin P v i L).toFinset

theorem mem_EE {v : Fin P.nV} {i : ℕ} {L L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)} :
    L'' ∈ EE P v i L ↔ IsEdge p (P.n' v) i ⟨L'', L⟩ :=
  Set.Finite.mem_toFinset _

theorem Tminus_eq (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) (L : P.Tup) :
    P.Tminus v i F L = ∑ L'' ∈ EE P v i (L v), F (Function.update L v L'') :=
  finsum_mem_eq_finite_toFinset_sum _ (edges_fin P v i (L v))

def TminusLin (v : Fin P.nV) (i : ℕ) : (P.Tup → P.Xsp) →ₗ[Kf] (P.Tup → P.Xsp) where
  toFun := P.Tminus v i
  map_add' F F' := by
    funext L
    rw [Pi.add_apply, Tminus_eq, Tminus_eq, Tminus_eq, ← Finset.sum_add_distrib]
    rfl
  map_smul' c F := by
    funext L
    rw [RingHom.id_apply, Pi.smul_apply, Tminus_eq, Tminus_eq, Finset.smul_sum]
    rfl

@[simp] theorem TminusLin_apply (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) :
    TminusLin P v i F = P.Tminus v i F := rfl

theorem edge_zero_iff {v : Fin P.nV} {L L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)} :
    IsEdge p (P.n' v) 0 ⟨L'', L⟩ ↔ IsLattice (P.W v) L ∧ L'' = L := by
  constructor
  · rintro ⟨_, h2, h3, _, h5⟩
    refine ⟨h2, le_antisymm h3 ?_⟩
    rw [Nat.mul_zero, pow_zero, Nat.card_eq_one_iff_unique] at h5
    have h6 := (Submodule.Quotient.subsingleton_iff).1 h5.1
    intro x hx
    have : (⟨x, hx⟩ : L) ∈ Submodule.comap L.subtype L'' := by
      have h7 : Submodule.comap L.subtype L'' = ⊤ := h6
      rw [h7]
      exact Submodule.mem_top
    exact this
  · rintro ⟨h, rfl⟩
    refine ⟨h, h, le_rfl, fun x hx => Submodule.smul_mem _ _ hx, ?_⟩
    rw [Nat.mul_zero, pow_zero, Nat.card_eq_one_iff_unique]
    have h7 : Submodule.comap (L''.subtype) L'' = ⊤ := Submodule.comap_subtype_self L''
    refine ⟨(Submodule.Quotient.subsingleton_iff).2 h7, ⟨0⟩⟩

theorem Tminus_zero_lat (v : Fin P.nV) (F : P.Tup → P.Xsp) (L : P.Tup) (hL : IsLattice (P.W v) (L v)) :
    P.Tminus v 0 F L = F L := by
  rw [Tminus_eq]
  have : EE P v 0 (L v) = {L v} := by
    ext A
    rw [mem_EE, edge_zero_iff, Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨hL, h⟩⟩
  rw [this, Finset.sum_singleton]
  exact congrArg F (Function.update_eq_self v L)

theorem Tminus_not_lat (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) (L : P.Tup) (hL : ¬ IsLattice (P.W v) (L v)) :
    P.Tminus v i F L = 0 := by
  rw [Tminus_eq]
  have : EE P v i (L v) = ∅ := by
    ext A
    rw [mem_EE]
    simp only [Finset.notMem_empty, iff_false]
    exact fun h => hL h.2.1
  rw [this, Finset.sum_empty]

end PlacesLevel

section SysLevel

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def TmLin (v : X.Pl) (i j : ℕ) : X.Fm j →ₗ[X.G.Kf] X.Fm j where
  toFun := X.Tm v i j
  map_add' F F' := by
    funext c
    exact (TminusLin (X.Pj j) (X.vJ j v) i).map_add (F c) (F' c)
  map_smul' a F := by
    funext c
    exact (TminusLin (X.Pj j) (X.vJ j v) i).map_smul a (F c)

@[simp] theorem TmLin_apply (v : X.Pl) (i j : ℕ) (F : X.Fm j) : TmLin X v i j F = X.Tm v i j F := rfl

def TtLin (v : X.Pl) (i j : ℕ) : X.Fm j →ₗ[X.G.Kf] X.Fm j :=
  if i = 0 then LinearMap.id else ((p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) j i)) • TmLin X v i j

@[simp] theorem TtLin_apply (v : X.Pl) (i j : ℕ) (F : X.Fm j) : TtLin X v i j F = X.Tt v i j F := by
  unfold TtLin Sys.Tt
  split_ifs <;> rfl

def TtuLin (v : X.Pl) (u : ℕ → X.G.Kf) (i j : ℕ) : X.Fm j →ₗ[X.G.Kf] X.Fm j :=
  ((∏ l ∈ Icc 1 j, u l) ^ (-(i : ℤ))) • TtLin X v i j

@[simp] theorem TtuLin_apply (v : X.Pl) (u : ℕ → X.G.Kf) (i j : ℕ) (F : X.Fm j) :
    TtuLin X v u i j F = X.Ttu v u i j F := by
  unfold TtuLin Sys.Ttu
  rw [LinearMap.smul_apply, TtLin_apply]

def ZopLin (v : X.Pl) (u m : ℕ → X.G.Kf) (j : ℕ) : X.Fm j →ₗ[X.G.Kf] X.Fm j :=
  ∑ l ∈ range (X.G.P.r + 1), ((-1 : X.G.Kf) ^ l * X.cl v m j l) • TtuLin X v u (X.G.P.r - l) j

@[simp] theorem ZopLin_apply (v : X.Pl) (u m : ℕ → X.G.Kf) (j : ℕ) (F : X.Fm j) :
    ZopLin X v u m j F = X.Zop v u m j F := by
  unfold ZopLin Sys.Zop
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [LinearMap.smul_apply, TtuLin_apply]

def ecalLin (v : X.Pl) (i j : ℕ) : X.Fm j →ₗ[X.G.Kf] X.Fm j :=
  ((p : X.G.Kf) ^ (-(((X.G.P.n' v / 2 : ℕ) : ℤ) * i * ((NN X.G.P.m X.t j : ℤ) - i)))) • TmLin X v i j

@[simp] theorem ecalLin_apply (v : X.Pl) (i j : ℕ) (F : X.Fm j) : ecalLin X v i j F = X.ecal v i j F := rfl

theorem yv_eq (v : X.Pl) (F : X.Fm 0) : X.yv v F = ((p : X.G.Kf) ^ X.G.P.ArV v) • X.Tm v X.G.P.r 0 F := rfl

def yvLin (v : X.Pl) : X.Fm 0 →ₗ[X.G.Kf] X.Fm 0 := ((p : X.G.Kf) ^ X.G.P.ArV v) • TmLin X v X.G.P.r 0

@[simp] theorem yvLin_apply (v : X.Pl) (F : X.Fm 0) : yvLin X v F = X.yv v F := rfl

theorem Int_zero_off {j : ℕ} {F : X.Fm j} (hF : F ∈ X.Int j) (c : X.Lv.comp j) (L : (X.Pj j).Tup)
    (hL : ¬ (X.Pj j).IsLatTup L) : F c L = 0 := by
  have h1 : F c ∈ (X.Lv.lev j c).M := hF c (Set.mem_univ c)
  unfold Level.M Level.funMod at h1
  have h2 : F c ∈ (⨅ (L : (X.Pj j).Tup) (_ : ¬ (X.Pj j).IsLatTup L),
      LinearMap.ker (LinearMap.proj (R := X.G.O) (φ := fun _ : (X.Pj j).Tup => (X.Pj j).Xsp) L)) := h1.1.2
  rw [Submodule.mem_iInf] at h2
  have h3 := h2 L
  rw [Submodule.mem_iInf] at h3
  exact h3 hL

theorem FQ_zero_off {j : ℕ} {F : X.Fm j} (hF : F ∈ X.FQ j) (c : X.Lv.comp j) (L : (X.Pj j).Tup)
    (hL : ¬ (X.Pj j).IsLatTup L) : F c L = 0 := by
  unfold Sys.FQ at hF
  induction hF using Submodule.span_induction with
  | mem x hx => exact Int_zero_off X hx c L hL
  | zero => rfl
  | add x y _ _ hx hy => rw [Pi.add_apply, Pi.add_apply, hx, hy, add_zero]
  | smul a x _ hx => rw [Pi.smul_apply, Pi.smul_apply, hx, smul_zero]

theorem Tm_zero {j : ℕ} (v : X.Pl) {F : X.Fm j} (hF : F ∈ X.FQ j) : X.Tm v 0 j F = F := by
  funext c L
  show (X.Pj j).Tminus (X.vJ j v) 0 (F c) L = F c L
  by_cases hL : IsLattice ((X.Pj j).W (X.vJ j v)) (L (X.vJ j v))
  · exact Tminus_zero_lat _ _ _ _ hL
  · rw [Tminus_not_lat _ _ _ _ _ hL, FQ_zero_off X hF c L fun h => hL (h _)]

theorem ecal_zero {j : ℕ} (v : X.Pl) {F : X.Fm j} (hF : F ∈ X.FQ j) : X.ecal v 0 j F = F := by
  unfold Sys.ecal
  rw [Tm_zero X v hF]
  simp

end SysLevel

end Formalism.MainNotions.FormalGroupSystem.Pf
