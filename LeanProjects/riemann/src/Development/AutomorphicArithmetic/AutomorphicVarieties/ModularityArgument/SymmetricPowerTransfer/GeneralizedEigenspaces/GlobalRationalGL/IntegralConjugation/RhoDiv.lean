import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.rhoDiv :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v w h (a : Kv v), P.φ v w h a ∈ w.adicCompletionIntegers L ↔ a ∈ v.adicCompletionIntegers (Lp L) := by
  intro L _ _ _ P v w h a
  subst h
  have hval : ∀ (F : Type) [Field F] [NumberField F] (u : Pl F) (x : F),
      Valued.v (algebraMap F (u.adicCompletion F) x) = u.valuation F x := fun F _ _ u x =>
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u x
  have he : (un w).asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (un w).ne_bot
  have key : ∀ x : Lp L, P.φ (un w) w rfl (cv (un w) x) ∈ w.adicCompletionIntegers L ↔
      cv (un w) x ∈ (un w).adicCompletionIntegers (Lp L) := by
    intro x
    have h1 := hval (Lp L) (un w) x
    have h2 := hval L w (algebraMap (Lp L) L x)
    rw [P.φ_alg, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, cv, h1, h2,
      ← IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L (un w) w x]
    first
      | exact pow_le_one_iff he
      | exact pow_le_one_iff_of_nonneg zero_le' he
      | exact pow_le_one_iff_of_nonneg (zero_le' (a := _)) he
  have hd : DenseRange (cv (un w)) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (Lp L) (un w)
  have hc := P.φ_cont (un w) w rfl
  have o1 : IsClopen ((P.φ (un w) w rfl) ⁻¹' (w.adicCompletionIntegers L : Set (Kw w))) :=
    (Valued.isClopen_integer (Kw w)).preimage hc
  have o2 : IsClopen ((un w).adicCompletionIntegers (Lp L) : Set (Kv (un w))) :=
    Valued.isClopen_integer (Kv (un w))
  constructor
  · intro ha
    by_contra hb
    obtain ⟨x, hx⟩ := hd.exists_mem_open (o1.isOpen.inter o2.compl.isOpen) ⟨a, ha, hb⟩
    exact hx.2 ((key x).1 hx.1)
  · intro ha
    by_contra hb
    obtain ⟨x, hx⟩ := hd.exists_mem_open (o2.isOpen.inter o1.compl.isOpen) ⟨a, ha, hb⟩
    exact hx.2 ((key x).2 hx.1)
