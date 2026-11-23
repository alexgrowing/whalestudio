import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagLineSection
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagLineDegree
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PNumericalSegre
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FlagBundleLineBaseProof

theorem intNum_eq_intNumL {K : Type*} [DecidableEq K] {ι : K → Type*} (F : Type*) [Field F]
    (P : Ideal (MRing ι F)) {n : ℕ} (bs : Fin n → K → ℤ) :
    intNum F P bs = intNumL F P (List.ofFn bs) := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get]

theorem pullDeg_some {K : Type*} (c : K → ℤ) :
    FieldNumbers.pullDeg (Function.Embedding.some : K ↪ Option K) c = liftDeg c := by
  funext o
  cases o with
  | none =>
    simp only [FieldNumbers.pullDeg, liftDeg, Option.elim]
    rw [Function.extend_apply']
    · rfl
    · rintro ⟨k, hk⟩
      exact Option.some_ne_none k hk
  | some k =>
    simp only [FieldNumbers.pullDeg, liftDeg, Option.elim]
    exact (Option.some_injective K).extend_apply c 0 k

theorem relDim_of_krull {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (F : Type)
    [Field F] (I : Ideal (MRing ι F)) (e : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    FieldNumbers.relDim I = ((e : ℕ) : WithBot (WithTop ℤ)) := by
  exact (FieldNumbers.CutRegular.relDim_eq_natCast_iff I e).2 h

theorem contractPrime_projIdeal {K : Type} {ι : K → Type} {Ω : Type} [Field Ω] {N M : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ] (F : Type)
    [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) :
    FieldNumbers.contractPrime (Function.Embedding.some : K ↪ Option K) (projIdeal F y w φ t) =
      pointIdeal (ι := fun k => bundleIdx ι M ((Function.Embedding.some : K ↪ Option K) k)) F y := by
  let ψ : MvPolynomial K Ω →+* MvPolynomial (Option K) Φ :=
    (rename (Option.some : K → Option K)).toRingHom.comp (MvPolynomial.map (algebraMap Ω Φ))
  have hψ : Function.Injective ψ :=
    (rename_injective _ (Option.some_injective K)).comp
      (MvPolynomial.map_injective _ (algebraMap Ω Φ).injective)
  unfold FieldNumbers.contractPrime projIdeal pointIdeal
  have hcomp : (eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
      (fun p => C (projCoord y w φ t p) * X p.1)).comp
      (rename (FieldNumbers.blockIncl (Function.Embedding.some : K ↪ Option K)
        (bundleIdx ι M))).toRingHom = ψ.comp (pointConeMap (ι := fun k => bundleIdx ι M ((Function.Embedding.some : K ↪ Option K) k))
        F y).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ, pointConeMap, MvPolynomial.algebraMap_eq]
    · rintro ⟨k, i⟩
      simp [ψ, pointConeMap, FieldNumbers.blockIncl, projCoord]
      rfl
  exact (RingHom.comap_ker _ _).trans
    ((congrArg RingHom.ker hcomp).trans (RingHom.ker_comp_of_injective _ hψ))

theorem replace_zeta {K : Type} [Fintype K] [DecidableEq K] {ι' : Option K → Type}
    [∀ o, Fintype (ι' o)] (F : Type) [Field F] (P : Ideal (MRing ι' F)) (hP : IsMultiProjPrime P)
    (e : ℕ) (hd : FieldNumbers.relDim P = ((e : ℕ) : WithBot (WithTop ℤ))) (c : K → ℤ)
    (bf bg : Option K → ℕ) (f g : MRing ι' F) (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg)
    (hfP : f ∉ P) (hgP : g ∉ P) (hfg : (fun o => (bf o : ℤ) - bg o) = zetaDeg - liftDeg c)
    (hdiv : ratDiv P f g = 0) :
    ∀ (n : ℕ) (Y : List (K → ℤ)), n + Y.length = e →
      intNumL F P (List.replicate n zetaDeg ++ Y.map liftDeg) =
        intNumL F P ((List.replicate n c ++ Y).map liftDeg) := by
  intro n
  induction n with
  | zero => intro Y _; simp
  | succ m ih =>
    intro Y hY
    set l := List.replicate m (zetaDeg : Option K → ℤ) ++ Y.map liftDeg with hl
    have hlen : l.length + 1 = e := by simp [hl]; omega
    have hdl : FieldNumbers.relDim P = ((l.length + 1 : ℕ) : WithBot (WithTop ℤ)) := by
      rw [hlen]; exact hd
    have hsplit : (zetaDeg : Option K → ℤ) = liftDeg c + (zetaDeg - liftDeg c) := by abel
    rw [List.replicate_succ, List.cons_append, ← hl, hsplit,
      NumericalSegreProof.intNumL_cons_add FieldNumbers.IntNumAdd.full F P hP l hdl]
    have hzero : intNumL F P ((zetaDeg - liftDeg c) :: l) = 0 := by
      rw [NumericalSegreProof.intNumL_perm F P (List.perm_append_singleton _ _).symm]
      have hcut := FieldNumbers.CutRational.full F (Option K) ι' P hP l.length hdl bf bg f g hf hg
        hfP hgP l.get
      rw [hfg, hdiv, intNum_eq_intNumL, List.ofFn_succ', List.concat_eq_append] at hcut
      simp only [Fin.snoc_castSucc, Fin.snoc_last, List.ofFn_get] at hcut
      rw [hcut]
      simp [cycEval]
    rw [hzero, add_zero]
    have hperm : (liftDeg c :: l).Perm
        (List.replicate m zetaDeg ++ (c :: Y).map liftDeg) := by
      rw [hl, List.map_cons]
      exact List.perm_middle.symm
    rw [NumericalSegreProof.intNumL_perm F P hperm, ih (c :: Y) (by simp; omega)]
    congr 1
    rw [List.replicate_succ', List.append_assoc, List.singleton_append]

end FlagBundleLineBaseProof

open FlagBundleLineBaseProof in

theorem FlagBundleLineBase.proof (hdim : FlagBundleDim.Statement)
    (hsec : FlagLineSection.Statement) (hdeg : FlagLineDegree.Statement)
    (hpf : FieldNumbers.ProjectionFormulaDegree.Statement.{0}) :
    FlagBundleLineBase.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hdimV N E _ _ B w b hflag M a φ hφ Φ _ _ t ht h0 n Y hnY
  obtain ⟨hP, hPd⟩ := hdim F Ω K ι y e hV hdimV N E B w b hflag M a φ hφ Φ t ht 1 le_rfl h0
  rw [show e + 1 - 1 = e by omega] at hPd
  obtain ⟨bf, bg, f, g, hf, hg, hfP, hgP, hfg, hdiv⟩ :=
    hsec F Ω K ι y e hV hdimV N E B w b hflag M a φ hφ Φ t ht h0
  rw [replace_zeta F _ hP e hPd (a - b ⟨0, h0⟩) bf bg f g hf hg hfP hgP hfg hdiv n Y hnY]
  set L := List.replicate n (a - b ⟨0, h0⟩) ++ Y with hL
  have hLlen : L.length = e := by simp [hL]; omega
  have hcon := contractPrime_projIdeal (K := K) F y w φ (truncCoord t 1)
  have hcd : FieldNumbers.relDim (FieldNumbers.contractPrime (Function.Embedding.some : K ↪ Option K)
      (projIdeal F y w φ (truncCoord t 1))) = ((L.length : ℕ) : WithBot (WithTop ℤ)) := by
    rw [hLlen]
    exact (congrArg FieldNumbers.relDim hcon).trans (relDim_of_krull F (pointIdeal F y) e hdimV)
  have hPd' : FieldNumbers.relDim (projIdeal F y w φ (truncCoord t 1)) =
      ((L.length : ℕ) : WithBot (WithTop ℤ)) := by
    rw [hLlen]; exact hPd
  have h := (hpf F K (Option K) Function.Embedding.some (bundleIdx ι M) _ hP L.length hPd' hcd
    L.get).2
  have h2 : intNum F (FieldNumbers.contractPrime (Function.Embedding.some : K ↪ Option K)
      (projIdeal F y w φ (truncCoord t 1))) L.get = intNum F (pointIdeal F y) L.get :=
    congrArg (fun I => intNum F I L.get) hcon
  rw [hdeg F Ω K ι y e hV hdimV N E B w b hflag M a φ hφ Φ t ht h0, Nat.cast_one, one_mul,
    h2] at h
  simp only [pullDeg_some] at h
  rw [intNum_eq_intNumL, intNum_eq_intNumL, List.ofFn_get] at h
  have hmap : List.ofFn (fun i => liftDeg (L.get i)) = L.map liftDeg := by
    apply List.ext_get <;> simp
  rw [hmap] at h
  exact h

end

end GroundTheory.Heights₂.Heights.NumbersDVR
