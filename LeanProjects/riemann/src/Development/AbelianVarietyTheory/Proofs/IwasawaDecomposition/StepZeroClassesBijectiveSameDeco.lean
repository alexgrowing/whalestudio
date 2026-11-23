import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Col2.ClsZero

section Canon
variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG)

def canon (d : DecoSet X.E n ST SG) : DecoSet X.E n ST SG :=
  Classical.epsilon (p := fun d' => ∃ (γ : UF X.E n) (k : Λ.grp),
    d' = ((γ, (k.1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG) • d) (h := ⟨d⟩)

theorem canon_spec (d : DecoSet X.E n ST SG) : ∃ (γ : UF X.E n) (k : Λ.grp),
    canon Λ d = ((γ, (k.1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG) • d :=
  Classical.epsilon_spec (p := fun d' => ∃ (γ : UF X.E n) (k : Λ.grp), d' = ((γ, (k.1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG) • d)
    ⟨d, 1, 1, (one_smul _ d).symm⟩

theorem canon_smul (γ : UF X.E n) (k : Λ.grp) (d : DecoSet X.E n ST SG) :
    canon Λ (((γ, (k.1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG) • d) = canon Λ d := by
  unfold canon
  congr 1
  funext d'
  apply propext
  constructor
  · rintro ⟨γ', k', rfl⟩
    exact ⟨γ' * γ, k' * k, by rw [← mul_smul]; rfl⟩
  · rintro ⟨γ', k', rfl⟩
    refine ⟨γ' * γ⁻¹, k' * k⁻¹, ?_⟩
    rw [← mul_smul]
    congr 1
    ext1 <;> simp

theorem canon_idem (d : DecoSet X.E n ST SG) : canon Λ (canon Λ d) = canon Λ d := by
  obtain ⟨γ, k, h⟩ := canon_spec Λ d
  conv_lhs => rw [h]
  exact canon_smul Λ γ k d

theorem orb_iff (y : Ys X n) (Λ' : LevFam X.E X.K n SG) (hΛ : Λ' = Λ) (Θ : LevQFam X.E X.K n Q) (hΘ : Θ = LevQFam.top X.E X.K n Q)
    (hy : y = Ys.triv X n) (p p' : PtY ST SG Q y) :
    (letI := ptYAct (ST := ST) y Λ' Θ; ∃ g : FrmG Λ' Θ, g • p = p') ↔ canon Λ p'.1.1.deco = canon Λ p.1.1.deco := by
  subst hΛ hΘ hy
  constructor
  · rintro ⟨g, rfl⟩
    exact canon_smul Λ' g.1 g.2.1 p.1.1.deco
  · intro h
    obtain ⟨γ₁, k₁, h₁⟩ := canon_spec Λ' p.1.1.deco
    obtain ⟨γ₂, k₂, h₂⟩ := canon_spec Λ' p'.1.1.deco
    have e : p'.1.1.deco = (((γ₂⁻¹ * γ₁ : UF X.E n), ((k₂⁻¹ * k₁ : Λ'.grp).1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG) • p.1.1.deco := by
      have := h₂.symm.trans (h.trans h₁)
      rw [← eq_inv_smul_iff, ← mul_smul] at this
      exact this
    generalize γ₂⁻¹ * γ₁ = γ at e
    generalize k₂⁻¹ * k₁ = k at e
    let q : DecoF X.E n ST SG Q := ((γ, k.1, 1) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • p.1.1
    have hq : q.deco = p'.1.1.deco := e.symm
    have hc : ∀ P : Q, (p'.1.1.fr P)⁻¹ * q.fr P ∈ GLint X.E n P.1 := by
      intro P x
      have h1 := q.2 P x
      have h2 := p'.1.1.2 P ((p'.1.1.fr P)⁻¹ (q.fr P x))
      have h3 : p'.1.1.1.2 P ((p'.1.1.fr P)⁻¹ (q.fr P x)) = q.fr P x := LinearEquiv.apply_symm_apply _ _
      rw [h3] at h2
      have h4 : q.1.1 = p'.1.1.1.1 := hq
      rw [h4] at h1
      exact h2.symm.trans h1
    refine ⟨(γ, k, ⟨fun P => ⟨_, hc P⟩, fun _ _ => trivial⟩), ?_⟩
    refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext e.symm ?_)) ?_)
    · funext P
      show γ.1 * p.1.1.fr P * ((p'.1.1.fr P)⁻¹ * (γ.1 * p.1.1.fr P * ((1 : GLQ X.E n Q) P)⁻¹.1))⁻¹ = p'.1.1.fr P
      simp only [Pi.one_apply, inv_one, OneMemClass.coe_one, mul_one]
      group
    · have h1 : p.1.2 = ∅ := p.2
      have h2 : p'.1.2 = ∅ := p'.2
      show (fun v => γ.1 v) '' p.1.2 = p'.1.2
      rw [h1, h2, Set.image_empty]

theorem eps_eq (y : Ys X n) (Λ' : LevFam X.E X.K n SG) (hΛ : Λ' = Λ) (Θ : LevQFam X.E X.K n Q) (p : PtY ST SG Q y) :
    (letI := ptYAct (ST := ST) y Λ' Θ
     Classical.epsilon (p := fun r => ∃ g : FrmG Λ' Θ, r = (g • p).1.1.deco) (h := ⟨p.1.1.deco⟩)) = canon Λ p.1.1.deco := by
  subst hΛ
  unfold canon
  congr 1
  funext r
  apply propext
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.1, g.2.1, rfl⟩
  · rintro ⟨γ, k, rfl⟩
    exact ⟨(γ, k, 1), rfl⟩

end Canon

attribute [local instance] starE
variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem levelTypePrimes_stepZero_eq_colLev (h : I.Ok) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0) :
    levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b = colLev I.Ch 0 := by
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 (by have := B.R.two_le_m; omega)) (by simp)
  · exact (h.idx_ok a).zero_G b

theorem chartIndexLevelTwistPrimes_stepZero_eq_top (h : I.Ok) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0) :
    levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b = LevQFam.top _ _ _ _ := by
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 (by have := B.R.two_le_m; omega)) (by simp)
  · exact (h.idx_ok a).zero_Q b

theorem ys0 (a : I.ι) : ysAt B.R I.sel (I.tup a) (I.cst a) 0 = Ys.triv _ _ :=
  if_neg (by have := B.R.two_le_m; omega)

theorem stepZero_chartIndex_subsingleton (h : I.Ok) (a : I.ι) (b b' : Idx I.sel (I.tup a) (I.idx a) 0) : b = b' := by
  have hm : 0 < B.R.m := by have := B.R.two_le_m; omega
  obtain ⟨b0, hb0⟩ := (h.idx_ok a).zero_uniq
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 hm) (by simp)
  obtain ⟨_ | b', hb'⟩ := b'
  · exact absurd (hb'.2 hm) (by simp)
  obtain rfl : b = b' := (hb0 b).trans (hb0 b').symm
  rfl

theorem stepZero_chartIndex_nonempty (h : I.Ok) (a : I.ι) : Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) := by
  obtain ⟨b0, -⟩ := (h.idx_ok a).zero_uniq
  exact ⟨⟨some b0, by have := B.R.two_le_m; simp; omega⟩⟩

theorem cl_eq_iff (h : I.Ok) (u : B.Word) (a : I.ι) (b b' : Idx I.sel (I.tup a) (I.idx a) 0) (p p' : PtAt B.R I.sel (I.tup a) (I.cst a) u 0) :
    (I.stp u a 0).cl b p = (I.stp u a 0).cl b' p' ↔ canon (colLev I.Ch 0) p.1.1.deco = canon (colLev I.Ch 0) p'.1.1.deco := by
  obtain rfl := stepZero_chartIndex_subsingleton h a b b'
  rw [← orb_iff (colLev I.Ch 0) _ _ (levelTypePrimes_stepZero_eq_colLev h a b) _ (chartIndexLevelTwistPrimes_stepZero_eq_top h a b) (ys0 a) p' p]
  constructor
  · intro e
    exact Quotient.exact (eq_of_heq (Sigma.mk.inj e).2)
  · intro e
    exact congrArg (Sigma.mk b) (Quotient.sound e)

theorem cl_rep {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (c : S.Cl) : S.cl c.1 (S.rep c) = c :=
  congrArg (Sigma.mk c.1) (S.rp_spec c.1 c.2)

theorem bij0 (h : I.Ok) (u : B.Word) (a : I.ι) (b) : Function.Bijective (I.cl0 u a b) := by
  constructor
  · intro c c' e
    have e1 := (cl_eq_iff h u a b b _ _).1 e
    rw [← cl_rep _ c, ← cl_rep _ c']
    exact (cl_eq_iff h u I.mu0 _ _ _ _).2 e1
  · intro c
    obtain ⟨b0⟩ := stepZero_chartIndex_nonempty h I.mu0
    refine ⟨(I.stp u I.mu0 0).cl b0 (I.pt0 u a I.mu0 ((I.stp u a 0).rep c)), ?_⟩
    have e := (cl_eq_iff h u I.mu0 _ _ _ _).1 (cl_rep _ ((I.stp u I.mu0 0).cl b0 (I.pt0 u a I.mu0 ((I.stp u a 0).rep c))))
    refine Eq.trans ?_ (cl_rep _ c)
    exact (cl_eq_iff h u a _ _ _ _).2 e

theorem stepZero_preferred_iff_canonicalRep (h : I.Ok) (u : B.Word) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0)
    (p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0) :
    I.pref u a 0 b p ↔ p.1.1.deco = canon (colLev I.Ch 0) p.1.1.deco := by
  have hm := B.R.two_le_m
  have e := eps_eq (ST := (B.primes X).vT u) (colLev I.Ch 0) _ _ (levelTypePrimes_stepZero_eq_colLev h a b)
    (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b) p
  constructor
  · intro hp
    exact Eq.trans (hp.1 rfl) e
  · intro hp
    exact ⟨fun _ => hp.trans e.symm, fun e' => absurd e' (by omega),
      topLev_pref_ne I.Ch I.sel (I.tup a) (I.cst a) I.Ps u (by omega) _⟩

theorem empty_mem_couplingIndexAtStep_zero (a : I.ι) (N) : ∅ ∈ (ysAt B.R I.sel (I.tup a) (I.cst a) 0).ys N := by
  rw [ys0]; rfl

theorem stepZero_representative_deco_eq_canonical (h : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) :
    ((I.stp u a 0).rep c).1.1.deco = canon (colLev I.Ch 0) ((I.stp u a 0).rep c).1.1.deco := by
  obtain ⟨b, q⟩ := c
  let p := (I.stp u a 0).rep ⟨b, q⟩
  obtain ⟨γ, k, e⟩ := canon_spec (colLev I.Ch 0) p.1.1.deco
  let p' : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 := ⟨(((γ, k.1, 1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs × GLQ B.fields.E (B.R.N 0) (I.Q a)) • p.1.1, ∅), empty_mem_couplingIndexAtStep_zero a _⟩
  have e' : p'.1.1.deco = canon (colLev I.Ch 0) p.1.1.deco := e.symm
  have hc : (I.stp u a 0).cl b p' = ⟨b, q⟩ := by
    refine Eq.trans ?_ (cl_rep _ ⟨b, q⟩)
    refine (cl_eq_iff h u a b b _ _).2 ?_
    rw [e', canon_idem]
  have hp := @pref_prefRep _ _ _ ((I.stp0 u a 0).actD b) (I.pref u a 0 b) p'
    ((stepZero_preferred_iff_canonicalRep h u a b p').2 (by rw [e', canon_idem]))
  have hq : q = Quotient.mk _ p' := (eq_of_heq (Sigma.mk.inj hc).2).symm
  refine (stepZero_preferred_iff_canonicalRep h u a b _).1 ?_
  rw [hq]
  exact hp

theorem stepZero_corresponding_representatives_same_deco (h : I.Ok) (u : B.Word) (a : I.ι) (b) (c : (I.stp u I.mu0 0).Cl) :
    ((I.stp u a 0).rep (I.cl0 u a b c)).1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
  refine (stepZero_representative_deco_eq_canonical h u a _).trans (Eq.trans ?_ (stepZero_representative_deco_eq_canonical h u I.mu0 c).symm)
  exact (cl_eq_iff h u a (I.cl0 u a b c).1 b ((I.stp u a 0).rep (I.cl0 u a b c))
    (I.pt0 u I.mu0 a ((I.stp u I.mu0 0).rep c))).1 (cl_rep (I.stp u a 0) (I.cl0 u a b c))

theorem stepZero_classes_bijective_same_deco : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a b,
    Function.Bijective (I.cl0 u a b) ∧
      ∀ c, ((I.stp u a 0).rep (I.cl0 u a b c)).1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco :=
  fun _ h u a b => ⟨bij0 h u a b, stepZero_corresponding_representatives_same_deco h u a b⟩

end GlobalTheory.Mem.Col2.ClsZero

end
