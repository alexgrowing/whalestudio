import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDeco
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwAtStd

theorem ptY_mv_deco {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}
    (p : PtY ST SG Q y) (d : DecoSet X.E n ST SG)
    (h1 : ∀ (P : Q) (x : Sp X.E n), p.1.1.1.2 P x ∈ d.1.at P.1 ↔ x ∈ stdAt X.E n P.1) (h2 : p.1.2 ∈ y.ys d.1.N) :
    (p.mv d).1.1.deco = d := by
  have e : p.mv d = (⟨(⟨(d, p.1.1.1.2), h1⟩, p.1.2), h2⟩ : PtY ST SG Q y) := dif_pos ⟨h1, h2⟩
  rw [e]
  rfl

theorem diaPt_deco (B : Base) (X : PreX B.toPre) (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ)
    (P : (B.primes X).vT u) (x : (Res P.1)ˣ) (c : (I.stp u a i).Cl) :
    (((I.atIn u a).A i).diaPt P x c).1.1.deco = DecoSet.dia1 P x ((I.stp u a i).rep c).1.1.deco :=
  ptY_mv_deco ((I.stp u a i).rep c) _ (fun Q y => ((I.stp u a i).rep c).1.1.2 Q y) ((I.stp u a i).rep c).2

theorem dil_eCls0 (B : Base) (X : PreX B.toPre) (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (P : (B.primes X).vT u) (x : (Res P.1)ˣ) (c : (I.stp u I.mu0 0).Cl) :
    (I.atIn u a).dil 0 P x (I.eCls0 l u a c) = I.eCls0 l u a ((I.atIn u I.mu0).dil 0 P x c) := by
  show (I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)) =
    I.cl0 u a (l.idx0 a).some ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))
  refine (ClsZero.cl_eq_iff hI u a _ _ _ _).2 ?_
  rw [diaPt_deco, ClsZero.stepZero_corresponding_representatives_same_deco hI]
  have e := (ClsZero.cl_eq_iff hI u I.mu0 _ _ _ _).1
    (ClsZero.cl_rep (I.stp u I.mu0 0) ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c)))
  show _ = ClsZero.canon _ ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco
  rw [e, diaPt_deco]

theorem deco_stab_trivial (B : Base) (X : PreX B.toPre) (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (b : (I.stp u a 0).β) (p : (I.stp u a 0).D b) (γ : UF B.fields.E (B.R.N 0)) (k : GLG B.fields.E (B.R.N 0) (B.primes X).vGs)
    (hk : k ∈ (colLev I.Ch 0).grp) (h : ((γ, k) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) • p.1.1.deco = p.1.1.deco) :
    γ = 1 ∧ k = 1 := by
  have hfree : (I.stp u a 0).Free := (l.lev u a).free0
  let q : DecoF B.fields.E (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (QE I.sel (I.tup a)) :=
    ((γ, k, 1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs × GLQ B.fields.E (B.R.N 0) (QE I.sel (I.tup a))) • p.1.1
  have hq : q.deco = p.1.1.deco := h
  have hc : ∀ P : QE I.sel (I.tup a), (p.1.1.fr P)⁻¹ * q.fr P ∈ GLint B.fields.E (B.R.N 0) P.1 := by
    intro P x
    have h1 := q.2 P x
    have h2 := p.1.1.2 P ((p.1.1.fr P)⁻¹ (q.fr P x))
    have h3 : p.1.1.1.2 P ((p.1.1.fr P)⁻¹ (q.fr P x)) = q.fr P x := LinearEquiv.apply_symm_apply _ _
    rw [h3] at h2
    have h4 : q.1.1 = p.1.1.1.1 := hq
    rw [h4] at h1
    exact h2.symm.trans h1
  have hkG : k ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b).grp := by rw [ClsZero.levelTypePrimes_stepZero_eq_colLev hI]; exact hk
  let qq : GLQ B.fields.E (B.R.N 0) (QE I.sel (I.tup a)) := fun P => ⟨(p.1.1.fr P)⁻¹ * q.fr P, hc P⟩
  have htop : ∀ Θ : LevQFam B.fields.E B.fields.K (B.R.N 0) (QE I.sel (I.tup a)), Θ = LevQFam.top _ _ _ _ → qq ∈ Θ.grp := by
    rintro _ rfl
    intro P _
    trivial
  have hqQ := htop _ (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI a b)
  have key : ∀ (y : Ys B.fields (B.R.N 0)), y = Ys.triv _ _ → ∀ (S : Set (Sp B.fields.E (B.R.N 0))) N, S ∈ y.ys N → S = ∅ := by
    rintro _ rfl S N hS
    exact hS
  have hp0 : p.1.2 = ∅ := key _ (ClsZero.ys0 a) _ _ p.2
  let g : (I.stp u a 0).G b := (γ, ⟨k, hkG⟩, ⟨qq, hqQ⟩)
  have hg : (I.stp u a 0).act b g p = p := by
    refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext h ?_)) ?_)
    · funext P
      show γ.1 * p.1.1.fr P * ((p.1.1.fr P)⁻¹ * (γ.1 * p.1.1.fr P * ((1 : GLQ B.fields.E (B.R.N 0) (QE I.sel (I.tup a))) P)⁻¹.1))⁻¹ = p.1.1.fr P
      simp only [Pi.one_apply, inv_one, OneMemClass.coe_one, mul_one]
      group
    · show (fun v => γ.1 v) '' p.1.2 = p.1.2
      rw [hp0, Set.image_empty]
  have e := hfree b g p hg
  exact ⟨congrArg Prod.fst e, congrArg (fun g : (I.stp u a 0).G b => (g.2.1 : GLG B.fields.E (B.R.N 0) (B.primes X).vGs)) e⟩

theorem chrG_eq {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (L Λ Λ' : LevFam E K n SG) (h : Λ = L) (h' : Λ' = L) (k : Λ.grp) (k' : Λ'.grp) (e : k.1 = k'.1) :
    Λ.chr k = Λ'.chr k' := by
  subst h h'
  rw [Subtype.ext e]

theorem chrQ_top {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))}
    (Θ : LevQFam E K n Q) (h : Θ = LevQFam.top E K n Q) (q : Θ.grp) : Θ.chr q = 1 := by
  subst h
  unfold LevQFam.chr piChar
  erw [Finset.prod_eq_one (fun i _ => MonoidHom.one_comp _)]
  rfl

theorem dilT_eCls0 (B : Base) (X : PreX B.toPre) (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (P : (B.primes X).vT u) (x : (Res P.1)ˣ) (c : (I.stp u I.mu0 0).Cl) :
    (I.atIn u a).dilT B.fields.emb B.embLL 0 P x (I.eCls0 l u a c) = (I.atIn u I.mu0).dilT B.fields.emb B.embLL 0 P x c := by
  show (I.stp u a 0).tr B.fields.emb B.embLL (I.cl0 u a (l.idx0 a).some c).1 ((I.stp u a 0).mv (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c))) = (I.stp u I.mu0 0).tr B.fields.emb B.embLL c.1 ((I.stp u I.mu0 0).mv c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))
  set ga := (I.stp u a 0).mv (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)) with hga
  set gm := (I.stp u I.mu0 0).mv c.1 (((I.atIn u I.mu0).A 0).diaPt P x c) with hgm
  have hA : ((ga.1, ga.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) •
      ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco = (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)).1.1.deco :=
    congrArg (fun p : (I.stp u a 0).D (I.cl0 u a (l.idx0 a).some c).1 => p.1.1.deco) ((I.stp u a 0).mv_smul (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))
  have hM : ((gm.1, gm.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) •
      ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco = (((I.atIn u I.mu0).A 0).diaPt P x c).1.1.deco :=
    congrArg (fun p : (I.stp u I.mu0 0).D c.1 => p.1.1.deco) ((I.stp u I.mu0 0).mv_smul c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))
  have hRA : ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco = ClsZero.canon (colLev I.Ch 0) (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)).1.1.deco :=
    (ClsZero.stepZero_representative_deco_eq_canonical hI u a _).trans ((ClsZero.cl_eq_iff hI u a _ _ _ _).1 (ClsZero.cl_rep (I.stp u a 0) ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))))
  have hRM : ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco = ClsZero.canon (colLev I.Ch 0) (((I.atIn u I.mu0).A 0).diaPt P x c).1.1.deco :=
    (ClsZero.stepZero_representative_deco_eq_canonical hI u I.mu0 _).trans ((ClsZero.cl_eq_iff hI u I.mu0 _ _ _ _).1 (ClsZero.cl_rep (I.stp u I.mu0 0) ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))))
  have hT : (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)).1.1.deco = (((I.atIn u I.mu0).A 0).diaPt P x c).1.1.deco := by
    rw [diaPt_deco, diaPt_deco, ClsZero.stepZero_corresponding_representatives_same_deco hI]
  have hR : ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco = ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco := by rw [hRA, hRM, hT]
  rw [hR, ← hT] at hM
  have hfix : (((gm.1, gm.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs)⁻¹ *
      ((ga.1, ga.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs)) •
      ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco = ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco := by
    rw [mul_smul, hA, inv_smul_eq_iff, hM]
  have memG : ∀ Λ : LevFam B.fields.E B.fields.K (B.R.N 0) (B.primes X).vGs, Λ = colLev I.Ch 0 → ∀ k : Λ.grp, k.1 ∈ (colLev I.Ch 0).grp := by
    rintro _ rfl k
    exact k.2
  have hkA := memG _ (ClsZero.levelTypePrimes_stepZero_eq_colLev hI a _) ga.2.1
  have hkM := memG _ (ClsZero.levelTypePrimes_stepZero_eq_colLev hI I.mu0 _) gm.2.1
  obtain ⟨e1, e2⟩ := deco_stab_trivial B X I hI l u a (I.cl0 u a (l.idx0 a).some c).1 ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))) (gm.1⁻¹ * ga.1) (gm.2.1.1⁻¹ * ga.2.1.1)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hkM) hkA) hfix
  have eγ : ga.1 = gm.1 := (inv_mul_eq_one.1 e1).symm
  have ek : ga.2.1.1 = gm.2.1.1 := (inv_mul_eq_one.1 e2).symm
  show trFr B.fields.emb B.embLL ((I.stp u a 0).gam (I.cl0 u a (l.idx0 a).some c).1 ga) ((I.stp u a 0).chr (I.cl0 u a (l.idx0 a).some c).1 ga) = trFr B.fields.emb B.embLL ((I.stp u I.mu0 0).gam c.1 gm) ((I.stp u I.mu0 0).chr c.1 gm)
  congr 1
  · show ufGL _ _ ga.1 = ufGL _ _ gm.1
    rw [eγ]
  · show (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 (I.cl0 u a (l.idx0 a).some c).1).chr ga.2.1 * (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 (I.cl0 u a (l.idx0 a).some c).1).chr ga.2.2 =
      (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr gm.2.1 * (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr gm.2.2
    rw [chrQ_top _ (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI a _), chrQ_top _ (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI I.mu0 _),
      chrG_eq (colLev I.Ch 0) _ _ (ClsZero.levelTypePrimes_stepZero_eq_colLev hI a _) (ClsZero.levelTypePrimes_stepZero_eq_colLev hI I.mu0 _) ga.2.1 gm.2.1 ek]

theorem mem_Fi_of_free {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (hS : S.Free)
    (φ : S.Cl → Col2.Fr emb σ n → ℂ) : φ ∈ S.Fi emb σ lam ↔ ∀ c, φ c ∈ ValC (Gr emb σ n) lam := by
  constructor
  · intro h c
    exact (h c).1
  · intro h c
    refine ⟨h c, fun g => ?_⟩
    have hg : g.1 = 1 := hS c.1 g.1 _ g.2
    funext y
    show S.tr emb σ c.1 g.1 (φ c) y = φ c y
    rw [hg]
    simp [GStep.tr, trFr_apply, frMul_one]

set_option maxHeartbeats 1000000 in

theorem twAtT_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), ∃ t : TwAtT (I.tw l l0 Z) u a, t.eVT = Equiv.refl _ ∧ ∀ v (r : 𝓞 B.host.E), t.eFv v (I.resT l u a v r) = I.resT l u I.mu0 (t.eVT v) r := by
  intro B X I hI hP l Z l0 u a
  refine ⟨
    { eVT := Equiv.refl _
      eFv := fun v => RingEquiv.refl _
      psiT := fun v x => rfl
      rhoT := by
        intro v x φ
        have e1 := dil_eCls0 B X I hI l u a v x
        have e2 := dilT_eCls0 B X I hI l u a v x
        funext c y
        obtain ⟨c', rfl⟩ := (I.eCls0 l u a).surjective c
        show (I.atIn u a).dilT B.fields.emb B.embLL 0 v x (I.eCls0 l u a c') (φ ((I.eCls0 l u a).symm ((I.atIn u a).dil 0 v x (I.eCls0 l u a c')))) y = (I.atIn u I.mu0).dilT B.fields.emb B.embLL 0 v x ((I.eCls0 l u a).symm (I.eCls0 l u a c')) (φ ((I.atIn u I.mu0).dil 0 v x ((I.eCls0 l u a).symm (I.eCls0 l u a c')))) y
        simp only [e1, e2, Equiv.symm_apply_apply]
      Mu0 := by
        show (I.stp u a 0).Fi B.fields.emb B.embLL (lamT (B.hcW u) 0) = Submodule.map (LinearEquiv.funCongrLeft ℂ (Col2.Fr B.fields.emb B.embLL (B.R.N 0) → ℂ) (I.eCls0 l u a).symm).toLinearMap ((I.stp u I.mu0 0).Fi B.fields.emb B.embLL (lamT (B.hcW u) 0))
        rw [Submodule.map_equiv_eq_comap_symm]
        ext ψ
        rw [Submodule.mem_comap, mem_Fi_of_free _ _ _ _ (l.lev u a).free0, mem_Fi_of_free _ _ _ _ (l.lev u I.mu0).free0]
        constructor
        · intro h c
          exact h _
        · intro h c
          obtain ⟨c', rfl⟩ := (I.eCls0 l u a).surjective c
          have := h c'
          simpa using this
      duStar := rfl
      Dstar := rfl
      GamP := rfl
      tauOf := fun w hw v => rfl
      seenP := fun w hw => rfl }, rfl, fun v r => rfl⟩

end GlobalTheory.Mem.Col2.TwAtStd

end
