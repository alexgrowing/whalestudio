import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open GlobalTheory.Mem.Col2

theorem stpTop_groupClasses : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι), (∀ c : (I.stp u a B.R.m).Cl, ∃ e : (I.stp u a B.R.m).G c.1 ≃ (UF B.host.E (B.R.N B.R.m) × ((I.Tp a).levG B.R.m).grp × ((I.Tp a).levQ B.R.m).grp), ∀ κ : (I.stp u a B.R.m).G c.1, (e κ).1 = κ.1 ∧ (I.stp u a B.R.m).gam c.1 κ = ufGL B.host.E (B.R.N B.R.m) (e κ).1 ∧ (I.stp u a B.R.m).chr c.1 κ = ((I.Tp a).levG B.R.m).chr (e κ).2.1 * ((I.Tp a).levQ B.R.m).chr (e κ).2.2 ∧ ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1 = (((e κ).1, (e κ).2.1.1, (e κ).2.2.1) : UF B.host.E (B.R.N B.R.m) × GLG B.host.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 ∧ cosetIn ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)) = cosetIn ((I.stp u a B.R.m).rep c) ∧ (((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1 = ((I.stp u a B.R.m).rep c).1.1 → (I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c) = (I.stp u a B.R.m).rep c)) ∧ (∀ (c c' : (I.stp u a B.R.m).Cl) (γ : UF B.host.E (B.R.N B.R.m)) (h : ((I.Tp a).levG B.R.m).grp) (θ : ((I.Tp a).levQ B.R.m).grp), ((γ, h.1, θ.1) : UF B.host.E (B.R.N B.R.m) × GLG B.host.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 = ((I.stp u a B.R.m).rep c').1.1 → c = c') ∧ (∀ p : DecoF B.host.E (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a), ∃ (c : (I.stp u a B.R.m).Cl) (γ : UF B.host.E (B.R.N B.R.m)) (h : ((I.Tp a).levG B.R.m).grp) (θ : ((I.Tp a).levQ B.R.m).grp), ((γ, h.1, θ.1) : UF B.host.E (B.R.N B.R.m) × GLG B.host.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 = p) ∧ Nonempty (I.stp u a B.R.m).Cl := by
  intro B X I u a
  have hne : B.R.m + 1 ≠ B.R.m := by omega
  have hY : ∀ p : PtAt (Pr := B.primes X) B.R I.sel (I.tup a) (I.cst a) u B.R.m, p.1.2 = ∅ := by
    intro p
    have h := p.2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hne] at h
    exact h
  have hpt : ∀ p q : PtAt (Pr := B.primes X) B.R I.sel (I.tup a) (I.cst a) u B.R.m, p.1.1 = q.1.1 → p = q := by
    intro p q h
    exact Subtype.ext (Prod.ext h ((hY p).trans (hY q).symm))
  have hcos : ∀ p q : PtAt (Pr := B.primes X) B.R I.sel (I.tup a) (I.cst a) u B.R.m, cosetIn p = cosetIn q := by
    intro p q
    funext P
    ext z
    simp [cosetIn, hY p, hY q]
  set S := I.stp u a B.R.m with hS
  have key : ∀ (T : GStep B.fields.E B.fields.K (B.R.N B.R.m)) (b : T.β) (x y : T.D b) (g : T.G b), g • x = y →
      (Quotient.mk (MulAction.orbitRel (T.G b) (T.D b)) x) = Quotient.mk (MulAction.orbitRel (T.G b) (T.D b)) y :=
    fun T b x y g h => Quotient.sound ⟨g⁻¹, by rw [← h]; exact inv_smul_smul g x⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨_ | al, hb⟩, q⟩
    · refine ⟨Equiv.refl _, fun κ => ⟨rfl, rfl, rfl, rfl, hcos _ _, fun h => hpt _ _ h⟩⟩
    · exact absurd (hb.1 rfl) (lt_irrefl _)
  · rintro ⟨⟨_ | al, hb⟩, q⟩ ⟨⟨_ | al', hb'⟩, q'⟩ γ h θ hγ
    · have e1 : S.act ⟨none, hb⟩ (γ, h, θ) (S.rep ⟨⟨none, hb⟩, q⟩) = S.rep ⟨⟨none, hb'⟩, q'⟩ := hpt _ _ hγ
      have hq : q = q' := by
        have h1 := S.rp_spec ⟨none, hb⟩ q
        have h2 := S.rp_spec ⟨none, hb'⟩ q'
        rw [← h1, ← h2]
        exact key S _ _ _ _ e1
      subst hq
      rfl
    · exact absurd (hb'.1 rfl) (lt_irrefl _)
    · exact absurd (hb.1 rfl) (lt_irrefl _)
    · exact absurd (hb.1 rfl) (lt_irrefl _)
  · intro p
    obtain ⟨pt, hpt'⟩ := exists_ptAt I.sel (I.tup a) (I.cst a) (R := B.R) (u := u) (j := B.R.m) p
    let b : S.β := Idx.top I.sel (I.tup a) (I.idx a) le_rfl
    obtain ⟨g, hg⟩ := S.exists_mv b pt
    refine ⟨S.cl b pt, g.1, g.2.1, g.2.2, ?_⟩
    exact (congrArg (fun x : PtAt (Pr := B.primes X) B.R I.sel (I.tup a) (I.cst a) u B.R.m => x.1.1) hg).trans hpt'
  · haveI : NeZero (B.R.N B.R.m) := ⟨by have := N_m_succ B.R; omega⟩
    obtain ⟨pt, -⟩ := exists_ptAt I.sel (I.tup a) (I.cst a) (R := B.R) (u := u) (j := B.R.m)
      (DecoF.base _ _ _ _ _)
    exact ⟨S.cl (Idx.top I.sel (I.tup a) (I.idx a) le_rfl) pt⟩

end GlobalTheory
