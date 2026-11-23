import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelEmbeddingInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem card_strictLower (n : ℕ) [Fintype {lk : Fin n × Fin n // lk.2 < lk.1}] :
    Fintype.card {lk : Fin n × Fin n // lk.2 < lk.1} = n.choose 2 := by
  let e : {lk : Fin n × Fin n // lk.2 < lk.1} ≃ Σ i : Fin n, Fin i.val :=
    { toFun := fun x => ⟨x.1.1, ⟨x.1.2.val, x.2⟩⟩
      invFun := fun y => ⟨(y.1, ⟨y.2.val, y.2.2.trans y.1.2⟩), y.2.2⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id, Nat.choose_two_right]

theorem choose_two_add (p q : ℕ) :
    (p + q).choose 2 = p * q + p.choose 2 + q.choose 2 := by
  induction q with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Nat.choose_succ_succ' (p + k) 1, Nat.choose_succ_succ' k 1, ih,
      Nat.choose_one_right, Nat.choose_one_right]
    ring

theorem dim_add_card_strictLower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H)
    (c : Coeff l) [Fintype (CMType H)] [Fintype (Σ s : CMType H ⊕ CMType H, {lk : Fin (labelRk D s) × Fin (labelRk D s) // lk.2 < lk.1})],
    D.dim + Fintype.card (Σ s : CMType H ⊕ CMType H, {lk : Fin (labelRk D s) × Fin (labelRk D s) // lk.2 < lk.1}) =
      Top.dimFl (CMType H) (D.p + D.q) := by
  intro E _ _ _ H D l c _ _
  have hc : 2 * Fintype.card (CMType H) = Module.finrank ℚ E := by
    have h := (GlobalTheory.CompanionTheory.Ar.labels_all_once E H l c).2
    rw [Nat.card_eq_fintype_card, Fintype.card_sum] at h
    omega
  have hs : Fintype.card (Σ s : CMType H ⊕ CMType H,
      {lk : Fin (labelRk D s) × Fin (labelRk D s) // lk.2 < lk.1}) =
      Fintype.card (CMType H) * D.p.choose 2 + Fintype.card (CMType H) * D.q.choose 2 := by
    classical
    rw [← Nat.card_eq_fintype_card, Nat.card_sigma, Fintype.sum_sum_type]
    simp only [Nat.card_eq_fintype_card]
    rw [Finset.sum_congr rfl (fun a _ => card_strictLower (labelRk D (Sum.inl a))),
      Finset.sum_congr rfl (fun a _ => card_strictLower (labelRk D (Sum.inr a)))]
    simp only [labelRk, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [hs, Top.dimFl, Datum.dim, ← hc, ← Nat.choose_two_right, choose_two_add,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  ring

end GlobalTheory.CompanionTheory.Ar.FlagStep
