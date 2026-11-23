import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmulOfDecoEq

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Mem.Col2.StepOk

theorem finite_orbits_of_finite_fibres {G A B : Type} [Group G] [MulAction G A] [MulAction G B] (π : A → B)
    (hπ : ∀ (g : G) a, π (g • a) = g • π a) (hf : ∀ b, {a | π a = b}.Finite)
    [Finite (MulAction.orbitRel.Quotient G B)] : Finite (MulAction.orbitRel.Quotient G A) := by
  haveI : ∀ b, Finite {a | π a = b} := fun b => (hf b).to_subtype
  refine Finite.of_surjective (fun x : Σ q : MulAction.orbitRel.Quotient G B, {a | π a = q.out} =>
    (Quotient.mk _ x.2.1 : MulAction.orbitRel.Quotient G A)) ?_
  intro c
  induction c using Quotient.inductionOn' with
  | h a =>
    have h : (MulAction.orbitRel G B).r (Quotient.mk (MulAction.orbitRel G B) (π a)).out (π a) :=
      Quotient.exact (Quotient.out_eq _)
    obtain ⟨g, hg⟩ := h
    refine ⟨⟨Quotient.mk _ (π a), ⟨g • a, (hπ g a).trans hg⟩⟩, ?_⟩
    exact Quotient.sound ⟨g, rfl⟩

theorem ufGL_mulVec {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) (x : Fin n → E) :
    ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x = γ.1 x :=
  LinearMap.toMatrix'_mulVec (γ.1 : Sp E n →ₗ[E] Sp E n) x

theorem ufGL_conjTranspose_mul {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) :
    ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)ᴴ *
      ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 := by
  ext a b
  have h : ∑ i, star (γ.1 (Pi.single a 1) i) * γ.1 (Pi.single b 1) i =
      ∑ i, star ((Pi.single a 1 : Fin n → E) i) * (Pi.single b 1 : Fin n → E) i :=
    γ.2 (Pi.single a 1) (Pi.single b 1)
  have hv : ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
    LinearMap.toMatrix' (γ.1 : Sp E n →ₗ[E] Sp E n) := rfl
  rw [hv, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · rw [Finset.sum_eq_single a]
    · simp [Matrix.one_apply, Pi.single_apply]
    · intro c _ hc
      simp [Pi.single_apply, hc]
    · simp

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem levQ_root (Θ : LevQFam X.E X.K n Q) (h : ∀ P g, ∃ m : ℕ, 0 < m ∧ (Θ P).lam g ^ m = 1) (g : Θ.grp) :
    ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1 := by
  rw [← isOfFinOrder_iff_pow_eq_one]
  unfold LevQFam.chr piChar
  erw [MonoidHom.finsetProd_apply]
  refine Finset.prod_induction _ IsOfFinOrder (fun _ _ ha hb => ha.mul hb) IsOfFinOrder.one fun P _ => ?_
  rw [isOfFinOrder_iff_pow_eq_one]
  exact h P _

theorem eq_one_of_fst (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (p : DecoF X.E n ST SG Q) (g : FrmG Λ Θ)
    (hg : FrmG.incl Λ Θ g • p = p) (h1 : g.1 = 1) : g = 1 := by
  have hb : FrmG.incl Λ Θ 1 • p = p := by rw [map_one, one_smul]
  have h2 := DecoSet.stab_fst_injective p.deco (a := ((FrmG.incl Λ Θ g).1, (FrmG.incl Λ Θ g).2.1))
    (b := ((FrmG.incl Λ Θ 1).1, (FrmG.incl Λ Θ 1).2.1)) (congrArg DecoF.deco hg) (congrArg DecoF.deco hb) h1
  exact FramedForms.incl_injective Λ Θ (FramedForms.stab_inj p hg hb h1 (Prod.mk.inj h2).2)

theorem stepY_ok : ∀ {X : Fields} {n : ℕ} {SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (y : Ys X n) (β : Type) [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q), X.Ok → ∀ (ST : Finset (HeightOneSpectrum (𝓞 X.E))) (pref : DecoF X.E n ST SG Q → Prop), (∀ b P, (Θ b P).H.FiniteIndex) → (∀ b P g, ∃ m : ℕ, 0 < m ∧ (Θ b P).lam g ^ m = 1) → (∀ N, Submodule.IsLattice X.E N → (y.ys N).Finite) → (stepY ST y β Λ Θ pref).Ok := by
  intro X n SG Q y β _ _ Λ Θ hX ST pref hfi hroot hfin
  have hG := fun b => FramedForms.main hX (ST := ST) (fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩) (Λ b) (Θ b) (hfi b)
    (levQ_root (Θ b) (hroot b))
  refine ⟨fun b => ?_, fun b p => ?_, fun b g => ?_, fun b g => ?_, fun b g p x => ?_, fun b p => ?_, fun b g p hg h1 => ?_⟩
  · letI := ptYAct (ST := ST) y (Λ b) (Θ b)
    haveI : Finite (MulAction.orbitRel.Quotient (FrmG (Λ b) (Θ b)) (DecoF X.E n ST SG Q)) := (hG b).fin_orb
    refine finite_orbits_of_finite_fibres (G := FrmG (Λ b) (Θ b)) (A := PtY ST SG Q y) (B := DecoF X.E n ST SG Q)
      (fun p => p.1.1) (fun _ _ => rfl) fun d => ?_
    refine Set.Finite.of_finite_image (f := fun p : PtY ST SG Q y => p.1.2) ?_ ?_
    · refine (hfin d.deco.1.N d.deco.2.1).subset ?_
      rintro _ ⟨p, hp, rfl⟩
      have hp' : p.1.1 = d := hp
      rw [← hp']
      exact p.2
    · intro p hp q hq h
      exact Subtype.ext (Prod.ext (hp.trans hq.symm) h)
  · letI := ptYAct (ST := ST) y (Λ b) (Θ b)
    haveI : Finite (MulAction.stabilizer (FrmG (Λ b) (Θ b)) p.1.1) := (hG b).fin_stab p.1.1
    refine Finite.of_injective (fun a : MulAction.stabilizer (FrmG (Λ b) (Θ b)) (show PtY ST SG Q y from p) =>
      (⟨a.1, congrArg (fun q : PtY ST SG Q y => q.1.1) a.2⟩ : MulAction.stabilizer (FrmG (Λ b) (Θ b)) p.1.1)) ?_
    intro a c h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  · exact ufGL_conjTranspose_mul g.1
  · obtain ⟨m, hm, hc⟩ := FramedForms.chr_root (Λ b) (Θ b) (levQ_root (Θ b) (hroot b)) g
    exact ⟨m, hm, Units.ext ((Units.val_pow_eq_pow_val _ _).trans hc)⟩
  · have h := p.1.1.deco.1.Lsh_act g.1.2 g.2.1.1
    show ((ufGL X.E n g.1 : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) *ᵥ x ∈ (p.1.1.deco.1.act g.1.1 g.2.1.1).Lsh ↔
      x ∈ p.1.1.deco.1.Lsh
    rw [h, ufGL_mulVec, mem_gmap, LinearEquiv.symm_apply_apply]
  · exact p.1.1.deco.2.Lsh_lattice
  · refine eq_one_of_fst (Λ b) (Θ b) p.1.1 g (congrArg (fun q : PtY ST SG Q y => q.1.1) hg) ?_
    have h2 : ufGL X.E n g.1 = 1 := h1
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rw [← ufGL_mulVec, h2]
    simp

end GlobalTheory.Mem.Col2.StepOk
