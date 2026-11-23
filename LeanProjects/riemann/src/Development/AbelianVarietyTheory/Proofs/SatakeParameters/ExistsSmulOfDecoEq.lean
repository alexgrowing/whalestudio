import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.ColFormsLemmas

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.FramedForms

section Torsor

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem deco_smul (a : UF E n × GLG E n SG × GLQ E n Q) (p : DecoF E n ST SG Q) :
    (a • p).deco = (a.1, a.2.1) • p.deco := rfl

theorem fr_smul (a : UF E n × GLG E n SG × GLQ E n Q) (p : DecoF E n ST SG Q) (P : Q) :
    (a • p).fr P = a.1.1 * p.fr P * ((a.2.2 P)⁻¹).1 := rfl

theorem exists_smul_of_deco_eq {p q : DecoF E n ST SG Q} (h : p.deco = q.deco) :
    ∃ c : GLQ E n Q, q = ((1, 1, c) : UF E n × GLG E n SG × GLQ E n Q) • p := by
  have h' : p.1.1 = q.1.1 := h
  refine ⟨fun P => ⟨(q.fr P)⁻¹ * p.fr P, fun x => ?_⟩, ?_⟩
  · have h1 := q.2 P (((q.fr P)⁻¹ * p.fr P) x)
    have h2 : q.1.2 P (((q.fr P)⁻¹ * p.fr P) x) = p.1.2 P x :=
      LinearEquiv.apply_symm_apply (q.1.2 P) (p.1.2 P x)
    rw [h2, ← h'] at h1
    exact h1.symm.trans (p.2 P x)
  · apply Subtype.ext
    apply Prod.ext
    · exact h'.symm.trans (one_smul (UF E n × GLG E n SG) p.1.1).symm
    · funext P
      show q.fr P = (1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * ((q.fr P)⁻¹ * p.fr P)⁻¹
      group

theorem stab_inj (p : DecoF E n ST SG Q) {a b : UF E n × GLG E n SG × GLQ E n Q}
    (ha : a • p = p) (hb : b • p = p) (h1 : a.1 = b.1) (h2 : a.2.1 = b.2.1) : a = b := by
  refine Prod.ext h1 (Prod.ext h2 ?_)
  funext P
  have e1 : (a • p).fr P = (b • p).fr P := by rw [ha, hb]
  rw [fr_smul, fr_smul, h1] at e1
  exact inv_injective (Subtype.ext (mul_left_cancel e1))

end Torsor

section Form

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem incl_injective (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) :
    Function.Injective (FrmG.incl Λ Θ) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun x => x.2.1) h
  have h3 := congrArg (fun x => x.2.2) h
  exact Prod.ext h1 (Prod.ext (Subtype.ext h2) (Subtype.ext h3))

theorem grp_finiteIndex (Θ : LevQFam X.E X.K n Q) (h : ∀ R : Q, (Θ R).H.FiniteIndex) :
    Θ.grp.FiniteIndex := by
  have h1 : ∀ R : Q, ((Θ R).H.comap (Pi.evalMonoidHom (fun P : Q => ↥(GLint X.E n P.1)) R)).FiniteIndex := by
    intro R
    refine ⟨?_⟩
    rw [Subgroup.index_comap_of_surjective _ (Function.surjective_eval R)]
    exact (h R).index_ne_zero
  have h2 := Subgroup.finiteIndex_iInf h1
  refine Subgroup.finiteIndex_of_le (H := ⨅ R : Q, (Θ R).H.comap
    (Pi.evalMonoidHom (fun P : Q => ↥(GLint X.E n P.1)) R)) ?_
  intro c hc
  exact (Subgroup.mem_pi _).mpr fun R _ => Subgroup.mem_iInf.mp hc R

theorem chr_root (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q)
    (hΘ : ∀ g, ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1) (g : FrmG Λ Θ) :
    ∃ m : ℕ, 0 < m ∧ ((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) ^ m = 1 := by
  obtain ⟨m, hm, hc⟩ := Λ.chr_root g.2.1
  obtain ⟨k, hk, hk'⟩ := hΘ g.2.2
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  have hk2 : ((Θ.chr g.2.2 : X.Kˣ) : X.K) ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, hk', Units.val_one]
  rw [Units.val_mul, mul_pow, pow_mul, hc, one_pow, one_mul, mul_comm m k, pow_mul, hk2, one_pow]

theorem frmGSD_ok (hX : X.Ok) (C : CoefPk X n (DecoSet X.E n ST SG)) (hC : C.Eqv)
    (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (hfi : ∀ R : Q, (Θ R).H.FiniteIndex)
    (hΘ : ∀ g, ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1) :
    (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ Θ).Ok where
  fin_orb := by
    obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
    have := grp_finiteIndex Θ hfi
    let T : Set (DecoSet X.E n ST SG) := {d | d ∈ s ∧ ∃ p : DecoF X.E n ST SG Q, p.deco = d}
    have hT : Finite T := hs.subset fun d hd => hd.1
    let S := frmGSD (C.pull (DecoF.deco (Q := Q))) Λ Θ
    refine Finite.of_surjective (fun x : T × (GLQ X.E n Q ⧸ Θ.grp) =>
      S.cls (((1, 1, (x.2.out)⁻¹) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • x.1.2.2.choose)) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h p =>
      obtain ⟨d0, hd0, g, hg⟩ := hrep (DecoF.deco p)
      have hq : (((g⁻¹, 1, 1) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • (p : DecoF X.E n ST SG Q)).deco = d0 := by
        rw [deco_smul, hg, smul_smul]
        simp only [Prod.mk_mul_mk, inv_mul_cancel, mul_one]
        exact one_smul (UF X.E n × GLG X.E n SG) d0
      have hd : d0 ∈ T := ⟨hd0, _, hq⟩
      obtain ⟨c, hc⟩ := exists_smul_of_deco_eq (hd.2.choose_spec.trans hq.symm)
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Θ.grp c⁻¹
      refine ⟨(⟨d0, hd⟩, (c⁻¹ : GLQ X.E n Q)), ?_⟩
      refine (S.cls_eq_iff _ p).mpr ⟨((g⁻¹, 1, h⁻¹) : FrmG Λ Θ), ?_⟩
      show ((g⁻¹, 1, (h : GLQ X.E n Q)⁻¹) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • (p : DecoF X.E n ST SG Q) =
        ((1, 1, ((c⁻¹ : GLQ X.E n Q) : GLQ X.E n Q ⧸ Θ.grp).out⁻¹) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) •
          hd.2.choose
      have e1 : ((g⁻¹, 1, (h : GLQ X.E n Q)⁻¹) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) =
          (1, 1, (h : GLQ X.E n Q)⁻¹) * (g⁻¹, 1, 1) := by simp
      rw [e1, mul_smul, hc, smul_smul, hh]
      simp
  fin_stab := by
    intro p
    have := DecoSet.finite_stabilizer (posStar_of_conj hX.conjE) (DecoF.deco p)
    refine Finite.of_injective
      (fun a : MulAction.stabilizer (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ Θ).G p =>
        (⟨((FrmG.incl Λ Θ a.1).1, (FrmG.incl Λ Θ a.1).2.1), congrArg DecoF.deco a.2⟩ :
          MulAction.stabilizer (UF X.E n × GLG X.E n SG) (DecoF.deco p))) ?_
    intro a b hab
    have h0 := congrArg Subtype.val hab
    exact Subtype.ext (incl_injective Λ Θ
      (stab_inj p a.2 b.2 (Prod.mk.inj h0).1 (Prod.mk.inj h0).2))
  nab_smul := by
    intro g p
    obtain ⟨m, hm, hc⟩ := chr_root Λ Θ hΘ g
    exact (hC.nab_smul ((FrmG.incl Λ Θ g).1, (FrmG.incl Λ Θ g).2.1) (DecoF.deco p)).trans
      (map_root_smul _ _ hm hc).symm
  del_smul := by
    intro g p
    obtain ⟨m, hm, hc⟩ := chr_root Λ Θ hΘ g
    exact (hC.del_smul ((FrmG.incl Λ Θ g).1, (FrmG.incl Λ Θ g).2.1) (DecoF.deco p)).trans
      (map_root_smul _ _ hm hc).symm
  inv := by
    intro g x y
    obtain ⟨m, hm, hc⟩ := chr_root Λ Θ hΘ g
    show C.pair (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) • C.rho g.1 x)
      (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) • C.rho g.1 y) = C.pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv g.1 x y, smul_smul]
    show (star ((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

theorem main : ∀ {X : Fields} (_ : X.Ok) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
    (lam : X.Tau → DomWeight n) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q),
    (∀ R : Q, (Θ R).H.FiniteIndex) → (∀ g, ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1) →
    (frmGSD ((roundPk X lam fun d : DecoSet X.E n ST SG => d.1.Lsh).pull DecoF.deco) Λ Θ).Ok := by
  intro X hX n ST SG Q lam Λ Θ h1 h2
  exact frmGSD_ok hX _
    ⟨fun a d => roundPk_nab X _ _ (d.1.Lsh_act a.1.2 a.2), fun a d => roundPk_del X _ _ (d.1.Lsh_act a.1.2 a.2),
      roundPk_inv X _ _ hX.emb_star⟩ Λ Θ h1 h2

end Form

end GlobalTheory.FramedForms
