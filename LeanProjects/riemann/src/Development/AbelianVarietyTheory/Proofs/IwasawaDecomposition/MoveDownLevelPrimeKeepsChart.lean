import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Formalism.LocalToGlobal.Columns.DecoratedFrameDiagonalTwistDecoration
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2

section Same

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

structure SameG {y : Ys X n} (p p' : PtY ST SG Q y) : Prop where
  fr : p'.1.1.1.2 = p.1.1.1.2
  ys : p'.1.2 = p.1.2
  at_eq : ∀ w : SG, p'.1.1.deco.1.at w.1 = p.1.1.deco.1.at w.1
  be : p'.1.1.deco.1.be = p.1.1.deco.1.be

theorem SameG.refl {y : Ys X n} (p : PtY ST SG Q y) : SameG p p :=
  ⟨rfl, rfl, fun _ => rfl, rfl⟩

private theorem locP_gmap_eq_of_locP_eq {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
    (g : Sp E n ≃ₗ[E] Sp E n) {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N) :
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g N') = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g N) := by
  have hs : ∀ (s : 𝓞 E) (z : Sp E n), g.symm (s • z) = s • g.symm z := fun s z =>
    ((g.symm : Sp E n →ₗ[E] Sp E n).restrictScalars (𝓞 E)).map_smul s z
  have hmemL : ∀ (M : Submodule (𝓞 E) (Sp E n)) (x : Sp E n),
      x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ↔ ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ M := fun _ _ => Iff.rfl

  have hmemg : ∀ (M : Submodule (𝓞 E) (Sp E n)) (x : Sp E n),
      x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g M) ↔ g.symm x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M := by
    intro M x
    rw [hmemL, hmemL]
    constructor
    · rintro ⟨s, hs0, hx⟩
      obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hx
      have hz' : z = g.symm (s • x) := by
        rw [← hzx]
        simp
      exact ⟨s, hs0, by rw [← hs, ← hz']; exact hz⟩
    · rintro ⟨s, hs0, hx⟩
      refine ⟨s, hs0, Submodule.mem_map.mpr ⟨g.symm (s • x), by rw [hs]; exact hx, by simp⟩⟩
  ext x
  rw [hmemg, hmemg, h]

theorem SameG.smul {y : Ys X n} {Λ : LevFam X.E X.K n SG} {Θ : LevQFam X.E X.K n Q} (h : FrmG Λ Θ) {p p' : PtY ST SG Q y}
    (r : SameG p p') : SameG ((ptYAct y Λ Θ).toSMul.smul h p) ((ptYAct y Λ Θ).toSMul.smul h p') where
  fr := congrArg (fun F => fun P => (FrmG.incl Λ Θ h).1.1 * F P * ((FrmG.incl Λ Θ h).2.2 P)⁻¹.1) r.fr
  ys := congrArg (fun S => (fun v => h.1.1 v) '' S) r.ys
  at_eq w := by
    show Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.HermitianLatticesTheory.gmap h.1.1 p'.1.1.deco.1.N) =
      Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.HermitianLatticesTheory.gmap h.1.1 p.1.1.deco.1.N)
    exact locP_gmap_eq_of_locP_eq w.1 h.1.1 (r.at_eq w)
  be := congrArg (fun B => fun w x => ((FrmG.incl Λ Θ h).2.1 w).1.mulVec (B w (h.1.1.symm x))) r.be

theorem SameG.dn {y : Ys X n} (p : PtY ST SG Q y) (P : ST) (hP : MoveHyp ST SG P) (f' : Sp X.E n → 𝓞 X.E ⧸ P.1.asIdeal) :
    SameG p (p.mv (p.1.1.deco.dn P f')) := by
  classical
  unfold PtY.mv
  refine Eq.mpr (apply_dite (SameG p) _ _ _) ?_
  split
  · refine ⟨rfl, rfl, fun w => ?_, ?_⟩
    · show (p.1.1.deco.dn P f').1.at w.1 = p.1.1.deco.1.at w.1
      unfold DecoSet.dn
      split_ifs with hok
      · exact ((p.1.1.deco.2.dnN_spec P hP.ne).2.2.1 w.1 (hP.sg w).1 (hP.sg w).2).localization_eq
      · rfl
    · show (p.1.1.deco.dn P f').1.be = p.1.1.deco.1.be
      unfold DecoSet.dn
      split_ifs <;> rfl
  · exact SameG.refl p

end Same

section Coset

private theorem cosetIn_eq_of_sameG' {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}
    {q q' : PtAt R sel mu cst u j} (r : SameG q q') : cosetIn q' = cosetIn q := by
  have hfr : ∀ P, frsF sel mu q'.1.1 P = frsF sel mu q.1.1 P := by
    intro P
    unfold frsF
    split_ifs with hP
    · unfold Deco.liftFr
      rw [r.at_eq ⟨P.1, hP⟩, r.be]
    · exact congrFun r.fr _
  funext P
  unfold cosetIn
  rw [r.ys, hfr P]

open Classical GlobalTheory.TopStep in

theorem cosetIn_eq_of_sameG {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (hX : X.Ok) (hPr : Pr.Ok)
    {q q' : PtAt R sel mu cst u j} (r : SameG q q') : cosetIn q' = cosetIn q :=
  cosetIn_eq_of_sameG' r

end Coset

section Normal

theorem prefRep_pref {G D : Type} [Group G] [MulAction G D] (pref : D → Prop) (q : MulAction.orbitRel.Quotient G D)
    (h : ∃ p, Quotient.mk (MulAction.orbitRel G D) p = q ∧ pref p) : pref (prefRep pref q) := by
  unfold prefRep
  rw [dif_pos h]
  exact h.choose_spec.2

theorem GStep.NormalFor.eq {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n} {b : S.β} {f : S.D b → A}
    {q q' : S.D b} (hq : S.NormalFor b f q) (hq' : S.NormalFor b f q')
    (h : ∀ r, (∃ g : S.G b, r = f (g • q)) ↔ ∃ g : S.G b, r = f (g • q')) : f q = f q' := by
  unfold GStep.NormalFor at hq hq'
  rw [hq, hq']
  exact congrArg (@Classical.epsilon A ⟨f q⟩) (funext fun r => propext (h r))

theorem GStep.exists_normalFor {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)
    (q : S.D b) : ∃ g : S.G b, S.NormalFor b f (g • q) := by
  have hex : ∃ r, ∃ g : S.G b, r = f (g • q) := ⟨f q, 1, by rw [one_smul]⟩
  obtain ⟨g, hg⟩ := Classical.epsilon_spec hex
  refine ⟨g, ?_⟩
  have hset : (fun r => ∃ g : S.G b, r = f (g • q)) = (fun r => ∃ g' : S.G b, r = f (g' • g • q)) := by
    funext r
    apply propext
    constructor
    · rintro ⟨g', rfl⟩
      exact ⟨g' * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩
    · rintro ⟨g', rfl⟩
      exact ⟨g' * g, by rw [mul_smul]⟩
  unfold GStep.NormalFor
  exact hg.symm.trans (congrArg (@Classical.epsilon A ⟨f q⟩) hset)

theorem GStep.prefRep_eq_of_normal {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)
    (pf : S.D b → Prop) (hn : ∀ q : MulAction.orbitRel.Quotient (S.G b) (S.D b), S.NormalFor b f (prefRep pf q)) (q : MulAction.orbitRel.Quotient (S.G b) (S.D b)) (d' : S.D b)
    (hd : ∀ h : S.G b, f (h • d') = f (h • prefRep pf q)) :
    f (prefRep pf (Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) d')) = f (prefRep pf q) := by
  obtain ⟨k, hk⟩ : ∃ k : S.G b, k • d' = prefRep pf (Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) d') :=
    Quotient.exact (prefRep_spec pf (Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) d'))
  refine GStep.NormalFor.eq (hn _) (hn q) fun r => ⟨?_, ?_⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g * k, by rw [← hk, ← mul_smul, hd]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g * k⁻¹, by rw [← hd, ← hk, mul_smul, inv_smul_smul]⟩

theorem GStep.prefRep_normal {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)
    (pf : S.D b → Prop) (hpf : ∀ p, pf p → S.NormalFor b f p) (hnp : ∀ p, S.NormalFor b f p → pf p)
    (q : MulAction.orbitRel.Quotient (S.G b) (S.D b)) : S.NormalFor b f (prefRep pf q) := by
  obtain ⟨g, hg⟩ := GStep.exists_normalFor S b f (Quotient.out q)
  have hex : ∃ p, Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) p = q ∧ pf p :=
    ⟨g • Quotient.out q, (Quotient.sound (s := MulAction.orbitRel (S.G b) (S.D b)) (MulAction.mem_orbit _ g)).trans
      (Quotient.out_eq q), hnp _ hg⟩
  exact hpf _ (prefRep_pref pf q hex)

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem TC.pref_of_normalFor (u : B.Word) (a : I.ι) (j : ℕ) (hj : j + 1 = B.R.m) (b : (I.stp0 u a j).β) (p : (I.stp0 u a j).D b)
    (h : (I.stp0 u a j).NormalFor b (fun q' : (I.stp0 u a j).D b => cosetIn q') p) : I.pref u a j b p := by
  have hm := B.R.two_le_m
  refine ⟨fun h0 => absurd hj (by omega), fun _ => h, ?_⟩
  show ∀ h : j = B.R.m, _
  intro hjm
  exact absurd hjm (by omega)

private theorem TC.cosetIn_rep_cl_dn_eq (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (i : ℕ) (v : (B.primes X).vT u)
    (c : (I.stp u a i).Cl) (f : Sp B.fields.E (B.R.N i) → Res v.1) :
    cosetIn ((I.stp u a i).rep ((I.stp u a i).cl c.1 (((I.atIn u a).A i).dn c.1 ((I.stp u a i).rep c) v f))) =
      cosetIn ((I.stp u a i).rep c) := by
  obtain ⟨b, q⟩ := c
  have r0 : SameG ((I.stp u a i).rep ⟨b, q⟩) (((I.atIn u a).A i).dn b ((I.stp u a i).rep ⟨b, q⟩) v f) :=
    SameG.dn _ v (moveHyp_of_ok hPr u v) f
  by_cases hi : i + 1 = B.R.m
  · exact GStep.prefRep_eq_of_normal (I.stp0 u a i) b (fun q' => cosetIn q') (I.pref u a i b)
      (GStep.prefRep_normal (I.stp0 u a i) b _ (I.pref u a i b) (fun p hp => hp.2.1 hi)
        (fun p hp => I.pref_of_normalFor u a i hi b p hp)) q _
      (fun h => cosetIn_eq_of_sameG' (SameG.smul h r0))
  ·
    have hemp : ∀ p : PtAt B.R I.sel (I.tup a) (I.cst a) u i, cosetIn p = fun _ => ∅ := by
      intro p
      have hys : ∀ (Y : Set (Sp B.fields.E (B.R.N i))) (N : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i))),
          Y ∈ (ysAt B.R I.sel (I.tup a) (I.cst a) i).ys N → Y = ∅ := by
        intro Y N hY
        unfold ysAt at hY
        rw [if_neg hi] at hY
        exact hY
      have hp : p.1.2 = ∅ := hys _ _ p.2
      funext P
      unfold cosetIn
      rw [hp]
      ext z
      simp
    exact (hemp _).trans (hemp _).symm

end Normal

theorem TC.dn_keeps_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → chOf ((I.fm l u a).dn i v c.1 g) = β := by
  intro B X I _ _ l Z u a i hi bad Ch chOf K eY eV L hK _ _ _ v β c g _

  obtain ⟨k, hR⟩ := hK
  exact ((hR.key ((I.fm l u a).dn i v c.1 g) c.1).mpr ⟨rfl, I.cosetIn_rep_cl_dn_eq l.pr u a i v c.1 _⟩).trans c.2

end GlobalTheory.Mem.Col2
