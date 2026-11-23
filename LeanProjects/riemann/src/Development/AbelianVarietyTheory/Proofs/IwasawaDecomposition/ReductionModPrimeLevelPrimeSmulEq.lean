import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvSmulMemOfRedL
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.LvProj

open GlobalTheory.LvT.Pts
open Formalism.HermitianLatticesTheory (localization₂ dual)

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {M A : Submodule (𝓞 E) (Fin n → E)} {P : HeightOneSpectrum (𝓞 E)}

theorem redL_osmul (r : 𝓞 E) {x : Fin n → E} (hx : x ∈ localization₂ P.asIdeal M) :
    redL M P (r • x) = (Ideal.Quotient.mk P.asIdeal r : Res P) • redL M P x := by
  obtain ⟨s, hs, hx⟩ := (mem_locP P M _).1 hx
  refine redL_eq hs (by rw [smul_comm]; exact M.smul_mem _ hx) ?_
  rw [smul_comm, redL_spec hs hx, mk_smul_mk]
  congr 1
  exact Subtype.ext (smul_comm _ _ _)

omit [StarRing E] in
theorem redL_zero : redL M P 0 = 0 := redL_coe (M := M) (P := P) 0

def proj (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) : A →+ TDat.Red M P where
  toFun z := redL M P z.1
  map_zero' := redL_zero
  map_add' x y := redL_add (h ▸ le_locP P A x.2) (h ▸ le_locP P A y.2)

theorem proj_mk (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) (z : A) (hz : z.1 ∈ M) :
    proj h z = Submodule.Quotient.mk ⟨z.1, hz⟩ := redL_coe (M := M) (P := P) ⟨z.1, hz⟩

theorem proj_smul (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) (a : 𝓞 E) (z : A) :
    proj h (a • z) = (Ideal.Quotient.mk P.asIdeal a : Res P) • proj h z :=
  redL_osmul a (h ▸ le_locP P A z.2)

theorem proj_surj (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) : Function.Surjective (proj h) := by
  intro y
  obtain ⟨x, hx, rfl⟩ := redL_surj y
  have hx' : x ∈ localization₂ P.asIdeal M := le_locP P M hx
  obtain ⟨s, hs, hsx⟩ := (mem_locP P A x).1 (h ▸ hx')
  obtain ⟨t, p, hp, e⟩ := P.isMaximal.exists_inv hs
  refine ⟨⟨(t * s) • x, by rw [mul_smul]; exact A.smul_mem _ hsx⟩, ?_⟩
  show redL M P ((t * s) • x) = _
  have e2 : (Ideal.Quotient.mk P.asIdeal (t * s) : Res P) = 1 := by
    rw [← map_one (Ideal.Quotient.mk P.asIdeal), ← e, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hp, add_zero]
  rw [redL_osmul _ hx', e2, one_smul]

theorem proj_ker (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) {J : Ideal (𝓞 E)} (hJ : J = P.asIdeal) (z : A) :
    proj h z = 0 ↔ z.1 ∈ J • A := by
  subst hJ
  show redL M P z.1 = 0 ↔ _
  constructor
  · intro h0
    obtain ⟨s, hs, hx⟩ := (mem_locP P M _).1 (h ▸ le_locP P A z.2)
    have h1 := redL_spec hs hx
    rw [h0, smul_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at h1
    have h2 := Submodule.mem_map_of_mem (f := M.subtype) h1
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at h2
    have key : P.asIdeal • M ≤ localization₂ P.asIdeal (P.asIdeal • A) := by
      rw [Submodule.smul_le]
      intro r hr y hy
      obtain ⟨t, ht, hty⟩ := (mem_locP P A y).1 (h ▸ le_locP P M hy)
      exact (mem_locP P _ _).2 ⟨t, ht, by rw [smul_comm]; exact Submodule.smul_mem_smul hr hty⟩
    obtain ⟨t, ht, h3⟩ := (mem_locP P _ _).1 (key h2)
    refine mem_smul_of_loc z.2 (s := t * s) (fun hm => (P.isPrime.mem_or_mem hm).elim ht hs) ?_
    rw [mul_smul]
    exact h3
  · intro hz
    have key : ∀ y ∈ P.asIdeal • A, y ∈ A ∧ redL M P y = 0 := by
      intro y hy
      refine Submodule.smul_induction_on hy (fun r hr w hw => ⟨A.smul_mem _ hw, ?_⟩) (fun y w hy hw => ⟨A.add_mem hy.1 hw.1, ?_⟩)
      · rw [redL_osmul r (h ▸ le_locP P A hw), Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_smul]
      · rw [redL_add (h ▸ le_locP P A hy.1) (h ▸ le_locP P A hw.1), hy.2, hw.2, add_zero]
    exact (key _ hz).2

end Red

section Dec

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem dualL_one (σ : E →+* E) (hσ : ∀ x, σ x = star x) {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1)
    (L : Submodule (𝓞 E) (Fin n → E)) : Formalism.L2.Forms.dualL σ J L = dual (hStd E n) L := by
  subst hJ
  have : Formalism.BasicNotions.dualSet σ (1 : Matrix (Fin n) (Fin n) E) L = (dual (hStd E n) L : Set (Fin n → E)) := by
    ext y
    rw [SetLike.mem_coe, Formalism.L2.Col.mem_dual]
    refine forall₂_congr fun x _ => ?_
    have e : Formalism.UG.hform σ (1 : Matrix (Fin n) (Fin n) E) x y = hStd E n x y := by
      show _ = ∑ i, star (x i) * y i
      unfold Formalism.UG.hform
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Matrix.one_apply, hσ]
    rw [e, Submodule.mem_one]
    rfl
  unfold Formalism.L2.Forms.dualL
  rw [this, Submodule.span_eq]

variable {d : Deco E n ST SG} {a : 𝓞 E}

theorem localization_L_eq_localization_dnN (hd : d.Ok) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) : localization₂ P.1.asIdeal d.L = localization₂ P.1.asIdeal (d.dnN P) := by
  rw [(hd.dnN_spec P hne).2.2.2]
  apply le_antisymm
  · refine localization_le_of_smul_mem (one_notMem P.1) fun x hx => ?_
    rw [one_smul]
    obtain ⟨h1, h2⟩ := (hd.mem_L x).1 hx
    exact (hd.mem_kerAt P x).2 ⟨h1, h2 P⟩
  · refine localization_le_of_le_localization _ fun x hx => ?_
    obtain ⟨h1, h2⟩ := (hd.mem_kerAt P x).1 hx
    exact (hd.mem_locP_L P x).2 ⟨le_locP _ _ h1, h2⟩

theorem sup_le_locP (hd : d.Ok) (ha : SepElt ST a) (P : ST) : d.L ⊔ P.1.asIdeal • d.Lsh ≤ localization₂ P.1.asIdeal d.L := by
  refine sup_le (le_locP _ _) ?_
  rw [Submodule.smul_le]
  intro r hr y hy
  have hy' := hd.Lsh_le_at ha P hy
  exact (hd.mem_locP_L P _).2 ⟨Submodule.smul_mem _ _ hy', by
    rw [hd.f_smul P r y hy', Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_mul]⟩

theorem localization_Lsh_eq_localization_N (hd : d.Ok) (ha : SepElt ST a) (P : ST) {A : Submodule (𝓞 E) (Fin n → E)} (hA : A = d.Lsh) :
    localization₂ P.1.asIdeal A = localization₂ P.1.asIdeal d.N := hA ▸ hd.locP_Lsh ha P

theorem localization_sup_eq_localization_dnN (hd : d.Ok) (ha : SepElt ST a) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) {A : Submodule (𝓞 E) (Fin n → E)}
    (hA : A = d.L ⊔ P.1.asIdeal • d.Lsh) : localization₂ P.1.asIdeal A = localization₂ P.1.asIdeal (d.dnN P) := by
  subst hA
  rw [← localization_L_eq_localization_dnN hd P hne]
  exact le_antisymm (localization_le_of_le_localization _ (sup_le_locP hd ha P))
    (localization_le_of_smul_mem (one_notMem P.1) fun x hx => by rw [one_smul]; exact Submodule.mem_sup_left hx)

theorem f_eq_zero_iff (hd : d.Ok) (ha : SepElt ST a) (P : ST) {z : Fin n → E} (hz : z ∈ d.Lsh) :
    d.f P z = 0 ↔ z ∈ d.L ⊔ P.1.asIdeal • d.Lsh := by
  constructor
  · intro h0
    obtain ⟨s, hs, hsz⟩ := (mem_locP _ _ _).1 ((hd.mem_locP_L P z).2 ⟨hd.Lsh_le_at ha P hz, h0⟩)
    obtain ⟨t, p, hp, e⟩ := P.1.isMaximal.exists_inv hs
    have : z = t • (s • z) + p • z := by rw [← mul_smul, ← add_smul, e, one_smul]
    rw [this]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ t hsz) (Submodule.smul_mem_smul hp hz)
  · intro h
    exact ((hd.mem_locP_L P z).1 (sup_le_locP hd ha P h)).2

theorem reductionModPrime_levelPrime_smul_eq (hd : d.Ok) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) {q : 𝓞 E} (hq : q ∈ P.1.asIdeal) {z e : Fin n → E}
    (hz : z ∈ d.at P.1) (hfz : d.f P z = 1) (he : e ∈ d.N) (hfe : d.f P e = 1) (t : d.dnN P) (ht : t.1 = q • e) :
    redL (d.dnN P) P.1 (q • z) = Submodule.Quotient.mk t := by
  have he' : e ∈ d.at P.1 := le_locP _ _ he
  have hn : (-1 : 𝓞 E) • e ∈ d.at P.1 := Submodule.smul_mem _ _ he'
  have m : z + (-1 : 𝓞 E) • e ∈ localization₂ P.1.asIdeal (d.dnN P) := by
    rw [← localization_L_eq_localization_dnN hd P hne]
    refine (hd.mem_locP_L P _).2 ⟨Submodule.add_mem _ hz hn, ?_⟩
    rw [hd.f_add P _ hz _ hn, hd.f_smul P _ _ he', hfz, hfe, map_neg, map_one]
    ring
  have e1 : q • z = q • (z + (-1 : 𝓞 E) • e) + t.1 := by
    rw [ht, neg_one_smul, ← smul_add, neg_add_cancel_right]
  rw [e1, redL_add (Submodule.smul_mem _ _ m) (le_locP _ _ t.2), redL_osmul _ m,
    Ideal.Quotient.eq_zero_iff_mem.2 hq, zero_smul, zero_add, redL_coe]

end Dec

section TD

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ}

theorem fv_mk (hl : A.Laws T) (P : ST) (c : S.Cl) (x : A.N c.1 (S.rep c)) :
    A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  have h0 := hl.fv_ne P c
  unfold TDat.fv at h0 ⊢
  split_ifs at h0 ⊢ with h1
  · exact h1.choose_spec x
  · exact absurd rfl h0

theorem te_mk (hl : A.Laws T) (P : ST) (c : S.Cl) :
    ∃ t : A.dnN c.1 (S.rep c) P, (∃ e ∈ A.N c.1 (S.rep c), A.f c.1 (S.rep c) P e = 1 ∧ (t : Fin n → E) = (T : 𝓞 E) • e) ∧
      Submodule.Quotient.mk t = A.te T P c := by
  have h0 := hl.te_ne P c
  unfold TDat.te at h0 ⊢
  split_ifs at h0 ⊢ with h1
  · exact ⟨h1.choose, h1.choose_spec, rfl⟩
  · exact absurd rfl h0

end TD

end GlobalTheory.Mem.Col2.LvProj

end

open GlobalTheory.Mem.Col2.LvProj GlobalTheory.LvT.Pts in
set_option maxHeartbeats 1600000 in

theorem GlobalTheory.Mem.Col2.TC.exists_level_projections : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∃ (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.IdL l Z u a i hi L := by
  intro B X I hI hP l Z u a i hi
  obtain ⟨-, -, -, hc⟩ := TC.spaces_in_coordinates I hI hP l Z
  obtain ⟨hg, -, hc⟩ := hc i hi
  have hL := (hc u a).1
  clear hc
  have ha := sepElt_of_ok l.pr u
  have hne : ∀ v : (B.primes X).vT u, conjPrime₂ v.1 ≠ v.1 := fun v => (moveHyp_of_ok l.pr u v).ne
  have hT : ∀ v : (B.primes X).vT u, ((B.T u : ℕ) : 𝓞 B.fields.E) ∈ v.1.asIdeal := fun v => Formalism.L2.Col.T_mem l.pr u v
  have hl := (l.fmL u a).lev i
  let d : (I.stp u a i).Cl → Deco B.fields.E (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs :=
    fun c => ((I.stp u a i).rep c).1.1.deco.1
  have hd : ∀ c, (d c).Ok := fun c => ((I.stp u a i).rep c).1.1.deco.2
  have hs : ∀ x : B.fields.E, (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) x = star x := fun _ => rfl
  have hD0 := fun L => @dualL_one B.fields.E B.fields.fieldE B.fields.nfE B.fields.starE _ _ hs _ hg L
  have hD : ∀ c, LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) = (d c).Lsh := fun c =>
    (hD0 _).trans (congrArg _ (hL c))
  have hPv : ∀ v : (B.primes X).vT u, PvG (D := I.rec7 l Z) (I.resT l u a) v = v.1.asIdeal := fun v =>
    Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem (I := (v.1.asIdeal : Ideal (𝓞 B.fields.E)))
  have hK : ∀ (v : (B.primes X).vT u) c, LkG (I.rec7 l Z) i hi (PvG (D := I.rec7 l Z) (I.resT l u a) v)
      (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) = (d c).L ⊔ v.1.asIdeal • (d c).Lsh := fun v c =>
    congrArg₂ (· ⊔ ·) (hL c) (congrArg₂ (· • ·) (hPv v) (hD c))
  have h1 := fun v c => localization_Lsh_eq_localization_N (hd c) ha v (hD c)
  have h2 := fun v c => localization_sup_eq_localization_dnN (hd c) ha v (hne v) (hK v c)
  have hf : ∀ v c z, (I.fm l u a).fv i v c (proj (h1 v c) z) = (d c).f v z.1 := fun v c z =>
    dual_redL ((hd c).f_smul v) _ (fv_mk hl v c) (h1 v c ▸ le_locP v.1 _ z.2)
  refine ⟨⟨fun v c => proj (h1 v c), fun v c => proj_surj (h1 v c), fun v c => proj_smul (h1 v c),
    fun v c => proj_ker (h1 v c) (hPv v), fun v c z => ?_, fun v c => proj (h2 v c), fun v c => proj_surj (h2 v c),
    fun v c => proj_smul (h2 v c), fun v c => proj_ker (h2 v c) (hPv v), fun v c z hz h => ?_⟩,
    fun v c z h => proj_mk (h1 v c) z h, fun v c z h => proj_mk (h2 v c) z h⟩
  · have e := f_eq_zero_iff (hd c) ha v (z := z.1) (hD c ▸ z.2)
    rw [← hK v c, ← hf v c z] at e
    exact e
  · obtain ⟨t, ⟨e, he, hfe, ht⟩, hte⟩ := te_mk hl v c
    exact (reductionModPrime_levelPrime_smul_eq (hd c) v (hne v) (hT v) ((hd c).Lsh_le_at ha v (hD c ▸ z.2)) ((hf v c z).symm.trans hz) he hfe t ht).trans hte
