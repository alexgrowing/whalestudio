import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.ColFormsLemmas

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem chfok_false (hQ : Q = ∅) (P : Q) : False := by
  obtain ⟨p, hp⟩ := P
  simp [hQ] at hp

def chfokLift (hQ : Q = ∅) (d : DecoSet X.E n ST SG) : DecoF X.E n ST SG Q :=
  ⟨(d, fun _ => 1), fun P _ => (chfok_false hQ P).elim⟩

theorem chfok_ext (hQ : Q = ∅) {p q : DecoF X.E n ST SG Q} (h : p.deco = q.deco) : p = q :=
  Subtype.ext (Prod.ext h (funext fun P => (chfok_false hQ P).elim))

theorem chfok_grp_one (hQ : Q = ∅) (Θ : LevQFam X.E X.K n Q) (c c' : ↥Θ.grp) : c = c' :=
  Subtype.ext (funext fun P => (chfok_false hQ P).elim)

theorem chfok_root (hQ : Q = ∅) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (g : FrmG Λ Θ) :
    ∃ m : ℕ, 0 < m ∧ (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) ^ m = 1 := by
  have h1 : g.2.2 = 1 := chfok_grp_one hQ Θ _ _
  obtain ⟨m, hm, hpow⟩ := LevFam.chr_root Λ g.2.1
  refine ⟨m, hm, ?_⟩
  rw [h1, map_one, mul_one]
  exact hpow

theorem frmGSD_ok_of_empty (hX : X.Ok) (hQ : Q = ∅) (C : CoefPk X n (DecoSet X.E n ST SG)) (hC : C.Eqv)
    (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) : (frmGSD (C.pull DecoF.deco) Λ Θ).Ok where
  fin_orb := by
    obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
    have : Finite s := hs
    refine Finite.of_surjective (fun d : s => (frmGSD (C.pull DecoF.deco) Λ Θ).cls (chfokLift hQ d.1)) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h p =>
      obtain ⟨d0, hd0, g, hg⟩ := hrep (DecoF.deco p)
      refine ⟨⟨d0, hd0⟩, ?_⟩
      refine ((frmGSD (C.pull DecoF.deco) Λ Θ).cls_eq_iff (chfokLift hQ d0) p).mpr ⟨((g, 1, 1) : FrmG Λ Θ)⁻¹, ?_⟩
      have h1 : p = (((g, 1, 1) : FrmG Λ Θ) : (frmGSD (C.pull DecoF.deco) Λ Θ).G) •
          (chfokLift hQ d0 : (frmGSD (C.pull DecoF.deco) Λ Θ).D) := chfok_ext hQ hg
      rw [h1, inv_smul_smul]
  fin_stab := by
    intro p
    have := DecoSet.finite_stabilizer (posStar_of_conj hX.conjE) (DecoF.deco p : DecoSet X.E n ST SG)
    refine Finite.of_injective
      (fun a : MulAction.stabilizer (frmGSD (C.pull DecoF.deco) Λ Θ).G p =>
        (⟨(a.1.1, (a.1.2.1 : GLG X.E n SG)), congrArg DecoF.deco a.2⟩ :
          MulAction.stabilizer (UF X.E n × GLG X.E n SG) (DecoF.deco p : DecoSet X.E n ST SG))) ?_
    intro a b hab
    have h0 : ((a.1.1, (a.1.2.1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG) = (b.1.1, (b.1.2.1 : GLG X.E n SG)) :=
      congrArg Subtype.val hab
    exact Subtype.ext (Prod.ext (Prod.mk.inj h0).1
      (Prod.ext (Subtype.ext (Prod.mk.inj h0).2) (chfok_grp_one hQ Θ _ _)))
  nab_smul := by
    intro g d
    obtain ⟨m, hm, hc⟩ := chfok_root hQ Λ Θ g
    exact (hC.nab_smul (g.1, (g.2.1 : GLG X.E n SG)) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm
  del_smul := by
    intro g d
    obtain ⟨m, hm, hc⟩ := chfok_root hQ Λ Θ g
    exact (hC.del_smul (g.1, (g.2.1 : GLG X.E n SG)) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm
  inv := by
    intro g (x : C.V) (y : C.V)
    obtain ⟨m, hm, hc⟩ := chfok_root hQ Λ Θ g
    show C.pair ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 x)
      ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 y) = C.pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv, smul_smul]
    show (star (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

end Gen

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

theorem chF_ok_of_QE (hX : X.Ok) (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (u : Pr.Word) (j : ℕ) : (chF W sel mu L u j).Ok := by
  intro b
  exact frmGSD_ok_of_empty hX hQ _ (colVal_eqv W hX u j (Pr.vT u) Pr.vGs) (L.levG j b) (L.levQ j b)

end Chain

end Formalism.L2.Col
