import Mathlib
import Formalism.LocalToGlobal.KernelLattices.MatrixKernelDiamondCommutation
import Formalism.GL3MeanSquares.HookFormulaTorsion.DoubleCosetDecompositionAll
import Formalism.LocalToGlobal.Columns.GSetLemmas
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.Columns.RowFormsSel
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.MemGoodPrimesOfNoExceptional
import Formalism.LocalToGlobal.Columns.TiedUpDnA
import Formalism.LocalToGlobal.Columns.DecoOwed

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Abs

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

theorem Nbr.count (n : Nbr S) (h : S.Ok) (s : S.Sec) {M : Type} [AddCommGroup M] [Module K M] (F : S.D → S.D → M)
    (hF : ∀ (g : S.G) (a b : S.D), F (g • a) (g • b) = F a b) :
    S.csOf h s (fun a => ∑ b ∈ n.up a, F a b) = S.csOf h s (fun b => ∑ a ∈ n.dn b, F a b) := by
  classical
  let _ := h.fintypeCl
  let _ : Module ℚ M := Module.compHom M (algebraMap ℚ K)
  have hinj : Function.Injective s.rep := fun c c' hc => by rw [← s.spec c, hc, s.spec]
  have hrep : ∀ a : S.D, ∃! r, r ∈ Finset.univ.image s.rep ∧ r ∈ MulAction.orbit S.G a := by
    intro a
    refine ⟨s.rep (S.cls a), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · exact (S.cls_eq_iff _ _).mp (s.spec _)
    · rintro r ⟨hr, hr2⟩
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
      have h1 : S.cls (s.rep c) = S.cls a := (S.cls_eq_iff _ _).mpr hr2
      rw [← h1, s.spec]
  have key := Formalism.HermitianLattices.RamifiedLatticeOperators.count_of_orbits S.G S.D S.D M n.up n.dn F (Finset.univ.image s.rep) (Finset.univ.image s.rep)
    (fun a b => n.mem_iff a b) (fun γ a b hb => (n.equiv γ a b).2 hb) (fun γ a b _ => hF γ a b) h.fin_stab h.fin_stab hrep hrep
  rw [Finset.sum_image (fun c _ c' _ hc => hinj hc), Finset.sum_image (fun c _ c' _ hc => hinj hc)] at key
  have hw : ∀ (c : S.Cl) (x : M), ((Nat.card (MulAction.stabilizer S.G (s.rep c)) : ℚ))⁻¹ • x = (((S.toCSDOf h s).wt c : K))⁻¹ • x := by
    intro c x
    show algebraMap ℚ K ((Nat.card (MulAction.stabilizer S.G (s.rep c)) : ℚ))⁻¹ • x = _
    rw [map_inv₀, map_natCast, GSD.wt_eq]
  simp only [hw] at key
  exact key

variable {S' : GSD K}

end Abs

section Abs3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S S' : GSD K}

end Abs3

section Abs3b

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

end Abs3b

section KerLin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {K : Type} [Field K] {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

omit [StarRing E] in

theorem kerOf_congr (th : ThDist E K a b SB V V') (Sall : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (N : Submodule (𝓞 E) (Sp E a)) (fr : Frs E a SB) (N' : Submodule (𝓞 E) (Sp E b)) (fr' : Frs E b SB)
    {Ξ Ξ' : HomE E a b → K} (h : ∀ x, Ξ x = Ξ' x) :
    kerOf th Sall cA cB N fr N' fr' Ξ = kerOf th Sall cA cB N fr N' fr' Ξ' := by
  rw [funext h]

end KerLin

section OffT

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end OffT

section OffTCh

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

variable {u : Pr.Word} {j : ℕ}

end OffTCh

section SumF

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

def replF (p : DecoF E n ST SG Q) (d₁ : DecoSet E n ST SG) (h : ∀ R : Q, d₁.1.at R.1 = p.deco.1.at R.1) : DecoF E n ST SG Q :=
  ⟨(d₁, p.1.2), fun R x => by
    show p.1.2 R x ∈ d₁.1.at R.1 ↔ _
    rw [h R]
    exact p.2 R x⟩

end SumF

section SumCh

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end SumCh

section Step3

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem mem_localization_of_smul_mem' (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E n)) {s : 𝓞 E} (hs : s ∉ P.asIdeal) {z : Sp E n}
    (h : s • z ∈ localization₂ P.asIdeal M) : z ∈ localization₂ P.asIdeal M := by
  obtain ⟨t, ht, htz⟩ := (mem_locP P M _).1 h
  exact (mem_locP P M z).2 ⟨t * s, fun hm => (P.isPrime.mem_or_mem hm).elim ht hs, by rw [mul_smul]; exact htz⟩

theorem localization_kerAt_eq {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (z : Sp E n) :
    z ∈ localization₂ P.1.asIdeal (d.kerAt P) ↔ z ∈ d.at P.1 ∧ d.f P z = 0 := by
  constructor
  · intro hz
    obtain ⟨s, hs, hsz⟩ := (mem_locP P.1 _ z).1 hz
    obtain ⟨h1, h2⟩ := (hd.mem_kerAt P _).1 hsz
    have hz' : z ∈ d.at P.1 := (mem_locP P.1 _ z).2 ⟨s, hs, h1⟩
    refine ⟨hz', ?_⟩
    rw [hd.f_smul P s z hz'] at h2
    exact (mul_eq_zero.1 h2).resolve_left (mk_ne_zero hs)
  · rintro ⟨hz, h0⟩
    obtain ⟨s, hs, hsz⟩ := (mem_locP P.1 _ z).1 hz
    refine (mem_locP P.1 _ z).2 ⟨s, hs, (hd.mem_kerAt P _).2 ⟨hsz, ?_⟩⟩
    rw [hd.f_smul P s z hz, h0, mul_zero]

theorem exists_f_one {d : Deco E n ST SG} (hd : d.Ok) (P : ST) : ∃ e ∈ d.N, d.f P e = 1 := by
  obtain ⟨x, hx, hne⟩ := hd.f_ne P
  have := P.1.isMaximal
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hne
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨t • x, Submodule.smul_mem _ t hx, by rw [hd.f_smul P t x (le_locP _ _ hx), mul_comm, hb]⟩

theorem f_sub {d : Deco E n ST SG} (hd : d.Ok) (P : ST) {y y' : Sp E n} (hy : y ∈ d.at P.1) (hy' : y' ∈ d.at P.1) :
    d.f P (y - y') = d.f P y - d.f P y' := by
  have e : y - y' = y + (-1 : 𝓞 E) • y' := by rw [neg_smul, one_smul, sub_eq_add_neg]
  rw [e, hd.f_add P y hy _ (Submodule.smul_mem _ _ hy'), hd.f_smul P _ y' hy', map_neg, map_one, neg_mul, one_mul, sub_eq_add_neg]

theorem isUp_facts {lo hi : Deco E n ST SG} (hlo : lo.Ok) {P : ST} (hP : MoveHyp ST SG P) {q : 𝓞 E} (hq : q ∈ P.1.asIdeal)
    (hq2 : q ∉ P.1.asIdeal ^ 2) (h : Deco.IsUp P q lo hi) :
    (∀ z, z ∈ lo.at P.1 ↔ z ∈ hi.at P.1 ∧ hi.f P z = 0) ∧ (∀ z ∈ hi.at P.1, hi.f P z = lo.f P (q • z)) ∧
      (∀ Q : ST, Q ≠ P → hi.at Q.1 = lo.at Q.1 ∧ hi.f Q = lo.f Q) := by
  obtain ⟨x, hx, hfx, rfl⟩ := h
  have hhi := hlo.up P hP hq hq2 hx hfx
  refine ⟨fun z => ?_, fun z hz => ?_, fun Q hQ => ⟨?_, lo.up_f_ne P q x hQ⟩⟩
  · rw [← localization_kerAt_eq hhi P z, ← (hhi.dnN_spec P hP.ne).2.2.2, hlo.dnN_up P hP hq hq2 hx hfx]
  · rw [Deco.up_f]
    exact if_pos hz
  · exact ((upN_spec hlo.lat hlo.uni P.1 hP.ne hx).2.2.1 Q.1 (fun h => hQ (Subtype.ext h)) (hP.st Q)).localization_eq

variable {a b : ℕ} {SG' : Finset (HeightOneSpectrum (𝓞 E))}

def PhiCond (d : Deco E a ST SG) (d' : Deco E b ST SG') (x : HomE E a b) : Prop :=
  ∀ Q : ST, ∀ y ∈ d.at Q.1, x y ∈ d'.at Q.1 ∧ d'.f Q (x y) = d.f Q y

theorem phiT_pos (K : Type) [Field K] {d : Deco E a ST SG} {d' : Deco E b ST SG'} {x : HomE E a b} (h : PhiCond d d' x) :
    phiT K d d' x = 1 := by
  unfold phiT
  exact if_pos h

theorem phiT_neg (K : Type) [Field K] {d : Deco E a ST SG} {d' : Deco E b ST SG'} {x : HomE E a b} (h : ¬ PhiCond d d' x) :
    phiT K d d' x = 0 := by
  unfold phiT
  exact if_neg h

def PhiMid (P : ST) (q : 𝓞 E) (d : Deco E a ST SG) (d' : Deco E b ST SG') (x : HomE E a b) : Prop :=
  (∀ Q : ST, Q ≠ P → ∀ y ∈ d.at Q.1, x y ∈ d'.at Q.1 ∧ d'.f Q (x y) = d.f Q y) ∧
    (∀ y ∈ d.at P.1, d.f P y = 0 → x y ∈ d'.at P.1) ∧ ∀ y ∈ d.at P.1, d'.f P (q • x y) = d.f P y

theorem phiMid_of_up {d : Deco E a ST SG} {d' e' : Deco E b ST SG'} (hd' : d'.Ok) {P : ST} (hP' : MoveHyp ST SG' P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) (h : Deco.IsUp P q d' e') {x : HomE E a b} (hx : PhiCond d e' x) :
    PhiMid P q d d' x := by
  obtain ⟨u1, u2, u3⟩ := isUp_facts hd' hP' hq hq2 h
  refine ⟨fun Q hQ y hy => ?_, fun y hy h0 => ?_, fun y hy => ?_⟩
  · have := hx Q y hy
    rw [(u3 Q hQ).1, (u3 Q hQ).2] at this
    exact this
  · have := hx P y hy
    exact (u1 _).2 ⟨this.1, this.2.trans h0⟩
  · have := hx P y hy
    rw [← u2 _ this.1]
    exact this.2

theorem phiMid_of_dn {d e : Deco E a ST SG} {d' : Deco E b ST SG'} (he : e.Ok) (hd : d.Ok) {P : ST} (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) (h : Deco.IsUp P q e d) {x : HomE E a b} (hx : PhiCond e d' x) :
    PhiMid P q d d' x := by
  obtain ⟨u1, u2, u3⟩ := isUp_facts he hP hq hq2 h
  refine ⟨fun Q hQ y hy => ?_, fun y hy h0 => ?_, fun y hy => ?_⟩
  · have := hx Q y (by rw [← (u3 Q hQ).1]; exact hy)
    rw [← (u3 Q hQ).2] at this
    exact this
  · exact (hx P y ((u1 y).2 ⟨hy, h0⟩)).1
  · have hqy : q • y ∈ e.at P.1 := (u1 _).2 ⟨Submodule.smul_mem _ q hy, by
      rw [hd.f_smul P q y hy, Ideal.Quotient.eq_zero_iff_mem.2 hq, zero_mul]⟩
    have := (hx P _ hqy).2
    rw [LinearMap.map_smul_of_tower] at this
    rw [this, u2 y hy]

theorem dn_unique {d e₁ e₂ : Deco E a ST SG} {d' : Deco E b ST SG'} (h₁ : e₁.Ok) (h₂ : e₂.Ok) {P : ST} {q : 𝓞 E}
    (k₁ : Deco.IsDn P q d e₁) (k₂ : Deco.IsDn P q d e₂) {x : HomE E a b} (x₁ : PhiCond e₁ d' x) (x₂ : PhiCond e₂ d' x) : e₁ = e₂ := by
  have hN : e₁.N = e₂.N := (congrArg Deco.N k₁.1).trans (congrArg Deco.N k₂.1).symm
  have hat : e₁.at P.1 = e₂.at P.1 := by
    show localization₂ _ e₁.N = localization₂ _ e₂.N
    rw [hN]
  have hf : e₁.f P = e₂.f P := by
    funext y
    by_cases hy : y ∈ e₁.at P.1
    · rw [← (x₁ P y hy).2, ← (x₂ P y (hat ▸ hy)).2]
    · rw [h₁.f_off P y hy, h₂.f_off P y (hat ▸ hy)]
  calc e₁ = d.dn P (e₁.f P) := k₁.1
    _ = d.dn P (e₂.f P) := by rw [hf]
    _ = e₂ := k₂.1.symm

theorem dn_exists {d : Deco E a ST SG} {d' : Deco E b ST SG'} (hd : d.Ok) (hd' : d'.Ok) {P : ST} (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) {x : HomE E a b} (hC : PhiMid P q d d' x) :
    ∃ e : Deco E a ST SG, e.Ok ∧ Deco.IsDn P q d e ∧ PhiCond e d' x := by
  classical
  obtain ⟨c1, c2, c3⟩ := hC
  let f' : Sp E a → 𝓞 E ⧸ P.1.asIdeal := fun y => if y ∈ localization₂ P.1.asIdeal (d.dnN P) then d'.f P (x y) else 0
  have hloc : ∀ y, y ∈ localization₂ P.1.asIdeal (d.dnN P) ↔ y ∈ d.at P.1 ∧ d.f P y = 0 := fun y => by
    rw [(hd.dnN_spec P hP.ne).2.2.2, localization_kerAt_eq hd]
  have hxin : ∀ y ∈ localization₂ P.1.asIdeal (d.dnN P), x y ∈ d'.at P.1 := fun y hy => c2 y ((hloc y).1 hy).1 ((hloc y).1 hy).2
  have hpos : ∀ y ∈ localization₂ P.1.asIdeal (d.dnN P), f' y = d'.f P (x y) := fun y hy => if_pos hy
  have hf1 : ∀ e0 ∈ d.N, d.f P e0 = 1 → f' (q • e0) = 1 := by
    intro e0 he0 h1
    rw [hpos _ (le_locP _ _ (le_sup_left (a := d.kerAt P) (hd.smul_mem_kerAt P hq he0))), LinearMap.map_smul_of_tower,
      c3 e0 (le_locP _ _ he0), h1]
  obtain ⟨e1, he1, hfe1⟩ := exists_f_one hd P
  have hOk : (d.dn P f').Ok := by
    refine hd.dn P hP (fun y hy y' hy' => ?_) (fun r y hy => ?_) (fun y hy => if_neg hy)
      ⟨q • e1, le_sup_left (a := d.kerAt P) (hd.smul_mem_kerAt P hq he1), by rw [hf1 e1 he1 hfe1]; exact one_ne_zero⟩
    · rw [hpos _ (Submodule.add_mem _ hy hy'), hpos _ hy, hpos _ hy', map_add, hd'.f_add P _ (hxin y hy) _ (hxin y' hy')]
    · rw [hpos _ (Submodule.smul_mem _ r hy), hpos _ hy, LinearMap.map_smul_of_tower, hd'.f_smul P r _ (hxin y hy)]
  have hfP : (d.dn P f').f P = f' := by simp [Deco.dn]
  refine ⟨d.dn P f', hOk, ⟨by rw [hfP], fun e0 he0 h1 => by rw [hfP]; exact hf1 e0 he0 h1⟩, fun Q y hy => ?_⟩
  by_cases hQ : Q = P
  · subst hQ
    have hy' : y ∈ localization₂ Q.1.asIdeal (d.dnN Q) := hy
    exact ⟨hxin y hy', by rw [hfP]; exact (hpos y hy').symm⟩
  · have hat : (d.dn P f').at Q.1 = d.at Q.1 :=
      ((hd.dnN_spec P hP.ne).2.2.1 Q.1 (fun h => hQ (Subtype.ext h)) (hP.st Q)).localization_eq
    have hfQ : (d.dn P f').f Q = d.f Q := Function.update_of_ne hQ _ _
    rw [hfQ]
    exact c1 Q hQ y (hat ▸ hy)

theorem q_ne_zero {P : HeightOneSpectrum (𝓞 E)} {q : 𝓞 E} (hq2 : q ∉ P.asIdeal ^ 2) : algebraMap (𝓞 E) E q ≠ 0 := by
  intro h
  apply hq2
  have : q = 0 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [h, map_zero]
  rw [this]
  exact Ideal.zero_mem _

theorem q_smul_inv {P : HeightOneSpectrum (𝓞 E)} {q : 𝓞 E} (hq2 : q ∉ P.asIdeal ^ 2) (w : Sp E n) :
    q • ((algebraMap (𝓞 E) E q)⁻¹ • w) = w := by
  rw [← algebraMap_smul E q, smul_smul, mul_inv_cancel₀ (q_ne_zero hq2), one_smul]

theorem up_diff_mem {d' : Deco E n ST SG} (hd' : d'.Ok) {P : ST} (hP' : MoveHyp ST SG P) {q : 𝓞 E} (hq : q ∈ P.1.asIdeal)
    (hq2 : q ∉ P.1.asIdeal ^ 2) {xW : Sp E n} (hxW : xW ∈ d'.N) (hfW : d'.f P xW = 1) :
    (algebraMap (𝓞 E) E q)⁻¹ • xW ∈ (d'.up P q xW).at P.1 ∧
      ∀ z ∈ (d'.up P q xW).at P.1, (d'.up P q xW).f P z = 1 → z - (algebraMap (𝓞 E) E q)⁻¹ • xW ∈ d'.at P.1 := by
  have hOk := hd'.up P hP' hq hq2 hxW hfW
  have hv := hd'.up_f_inv P hP' hq hq2 hxW hfW
  have hvm : (algebraMap (𝓞 E) E q)⁻¹ • xW ∈ (d'.up P q xW).at P.1 := by
    by_contra hc
    rw [hOk.f_off P _ hc] at hv
    exact zero_ne_one hv
  refine ⟨hvm, fun z hz h1 => ?_⟩
  exact ((isUp_facts hd' hP' hq hq2 ⟨xW, hxW, hfW, rfl⟩).1 _).2 ⟨Submodule.sub_mem _ hz hvm, by
    rw [f_sub hOk P hz hvm, h1, hv, sub_self]⟩

theorem up_unique {d : Deco E a ST SG} {d' e₁ e₂ : Deco E b ST SG'} (hd : d.Ok) (hd' : d'.Ok) {P : ST} (hP' : MoveHyp ST SG' P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) (k₁ : Deco.IsUp P q d' e₁) (k₂ : Deco.IsUp P q d' e₂) {x : HomE E a b}
    (x₁ : PhiCond d e₁ x) (x₂ : PhiCond d e₂ x) : e₁ = e₂ := by
  obtain ⟨w₁, hw₁, hf₁, rfl⟩ := k₁
  obtain ⟨w₂, hw₂, hf₂, rfl⟩ := k₂
  apply Deco.up_congr
  obtain ⟨e1, he1, hfe1⟩ := exists_f_one hd P
  have he1P : e1 ∈ d.at P.1 := le_locP _ _ he1
  have m₁ := (up_diff_mem hd' hP' hq hq2 hw₁ hf₁).2 (x e1) (x₁ P e1 he1P).1 ((x₁ P e1 he1P).2.trans hfe1)
  have m₂ := (up_diff_mem hd' hP' hq hq2 hw₂ hf₂).2 (x e1) (x₂ P e1 he1P).1 ((x₂ P e1 he1P).2.trans hfe1)
  have m : (algebraMap (𝓞 E) E q)⁻¹ • w₁ - (algebraMap (𝓞 E) E q)⁻¹ • w₂ ∈ d'.at P.1 := by
    have := Submodule.sub_mem _ m₂ m₁
    rwa [sub_sub_sub_cancel_left] at this
  obtain ⟨s, hs, hsm⟩ := (mem_locP P.1 _ _).1 m
  refine mem_smul_of_loc (Submodule.sub_mem _ hw₁ hw₂) hs ?_
  have e : s • (w₁ - w₂) = q • (s • ((algebraMap (𝓞 E) E q)⁻¹ • w₁ - (algebraMap (𝓞 E) E q)⁻¹ • w₂)) := by
    rw [smul_comm q s, smul_sub q, q_smul_inv hq2, q_smul_inv hq2]
  rw [e]
  exact Submodule.smul_mem_smul hq hsm

theorem inv_smul_q {P : HeightOneSpectrum (𝓞 E)} {q : 𝓞 E} (hq2 : q ∉ P.asIdeal ^ 2) (w : Sp E n) :
    (algebraMap (𝓞 E) E q)⁻¹ • (q • w) = w := by
  rw [← algebraMap_smul E q, smul_smul, inv_mul_cancel₀ (q_ne_zero hq2), one_smul]

theorem up_exists {d : Deco E a ST SG} {d' : Deco E b ST SG'} (hd : d.Ok) (hd' : d'.Ok) {P : ST} (hP' : MoveHyp ST SG' P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) {x : HomE E a b} (hC : PhiMid P q d d' x) :
    ∃ e' : Deco E b ST SG', e'.Ok ∧ Deco.IsUp P q d' e' ∧ PhiCond d e' x := by
  obtain ⟨c1, c2, c3⟩ := hC
  obtain ⟨e1, he1, hfe1⟩ := exists_f_one hd P
  have he1P : e1 ∈ d.at P.1 := le_locP _ _ he1
  have hqz : q • x e1 ∈ d'.at P.1 := by
    have := c2 (q • e1) (Submodule.smul_mem _ q he1P) (by
      rw [hd.f_smul P q e1 he1P, Ideal.Quotient.eq_zero_iff_mem.2 hq, zero_mul])
    rwa [LinearMap.map_smul_of_tower] at this
  have hfqz : d'.f P (q • x e1) = 1 := (c3 e1 he1P).trans hfe1
  obtain ⟨s, hs, hsz⟩ := (mem_locP P.1 _ _).1 hqz
  obtain ⟨t, p, hp, e⟩ := P.1.isMaximal.exists_inv hs
  obtain ⟨xW, hxWdef⟩ : ∃ xW, xW = (t * s) • (q • x e1) := ⟨_, rfl⟩
  have hxW : xW ∈ d'.N := by
    rw [hxWdef, mul_smul]
    exact Submodule.smul_mem _ t hsz
  have hmk : Ideal.Quotient.mk P.1.asIdeal (t * s) = 1 := by
    have h1 : t * s = 1 - p := by rw [← e]; ring
    rw [h1, map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.2 hp, sub_zero]
  have hfW : d'.f P xW = 1 := by
    rw [hxWdef, hd'.f_smul P _ _ hqz, hmk, hfqz, mul_one]
  have hup : Deco.IsUp P q d' (d'.up P q xW) := ⟨xW, hxW, hfW, rfl⟩
  obtain ⟨u1, u2, u3⟩ := isUp_facts hd' hP' hq hq2 hup
  have hOk := hd'.up P hP' hq hq2 hxW hfW
  have hvm := (up_diff_mem hd' hP' hq hq2 hxW hfW).1
  have hpz : p • x e1 ∈ d'.at P.1 := by
    obtain ⟨a', ha', r, hr, har⟩ := exists_inv_unif P.1 hq hq2
    obtain ⟨c, hc⟩ := neighbourConstruct_mem_inv.1 ha' p hp
    refine mem_localization_of_smul_mem' P.1 _ hr ?_
    have h1 : r • (p • x e1) = c • (q • x e1) := by
      rw [← algebraMap_smul E r, ← algebraMap_smul E p, ← algebraMap_smul E c, ← algebraMap_smul E q, smul_smul, smul_smul, ← har, hc]
      congr 1
      ring
    rw [h1]
    exact Submodule.smul_mem _ c hqz
  have hz : x e1 ∈ (d'.up P q xW).at P.1 := by
    have h1 : (algebraMap (𝓞 E) E q)⁻¹ • xW = (t * s) • x e1 := by
      rw [hxWdef, smul_comm, inv_smul_q hq2]
    have h2 : x e1 = (algebraMap (𝓞 E) E q)⁻¹ • xW + p • x e1 := by
      rw [h1, ← add_smul, e, one_smul]
    rw [h2]
    exact Submodule.add_mem _ hvm ((u1 _).1 hpz).1
  refine ⟨_, hOk, hup, fun Q y hy => ?_⟩
  by_cases hQ : Q = P
  · subst hQ
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (d.f Q y)
    have hce : c • e1 ∈ d.at Q.1 := Submodule.smul_mem _ c he1P
    have hx0 : x (y - c • e1) ∈ d'.at Q.1 := c2 _ (Submodule.sub_mem _ hy hce) (by
      rw [f_sub hd Q hy hce, hd.f_smul Q c e1 he1P, hfe1, mul_one, hc, sub_self])
    have hxy : x y ∈ (d'.up Q q xW).at Q.1 := by
      have h1 : x y = x (y - c • e1) + c • x e1 := by rw [map_sub, LinearMap.map_smul_of_tower, sub_add_cancel]
      rw [h1]
      exact Submodule.add_mem _ ((u1 _).1 hx0).1 (Submodule.smul_mem _ c hz)
    exact ⟨hxy, by rw [u2 _ hxy]; exact c3 y hy⟩
  · rw [(u3 Q hQ).1, (u3 Q hQ).2]
    exact c1 Q hQ y hy

theorem mem_upFin (d' e' : DecoSet E n ST SG) (P : ST) (q : 𝓞 E) :
    e' ∈ (DecoSet.upSet_finite d' P q).toFinset ↔ Deco.IsUp P q d'.1 e'.1 := Set.Finite.mem_toFinset _

theorem mem_dnFin (d e : DecoSet E n ST SG) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) (q : 𝓞 E) :
    e ∈ (DecoSet.dnSet_finite d P hne q).toFinset ↔ Deco.IsDn P q d.1 e.1 := Set.Finite.mem_toFinset _

theorem phiStep (K : Type) [Field K] {P : ST} {q : 𝓞 E} (hP : MoveHyp ST SG P) (hP' : MoveHyp ST SG' P) (hq : q ∈ P.1.asIdeal)
    (hq2 : q ∉ P.1.asIdeal ^ 2) (d : DecoSet E a ST SG) (d' : DecoSet E b ST SG') : PhiStep K P q hP.ne d d' := by
  classical
  intro x
  by_cases hC : PhiMid P q d.1 d'.1 x
  · obtain ⟨e', he', hu, hx'⟩ := up_exists d.2 d'.2 hP' hq hq2 hC
    obtain ⟨e, he, hdn, hx⟩ := dn_exists d.2 d'.2 hP hq hC
    have hL : ∑ e' ∈ (DecoSet.upSet_finite d' P q).toFinset, phiT K d.1 e'.1 x = 1 := by
      rw [Finset.sum_eq_single_of_mem (⟨e', he'⟩ : DecoSet E b ST SG') ((mem_upFin d' ⟨e', he'⟩ P q).2 hu) (fun e2 h2 hne =>
        phiT_neg K fun hx2 => hne (Subtype.ext (up_unique d.2 d'.2 hP' hq hq2 ((mem_upFin d' e2 P q).1 h2) hu hx2 hx')))]
      exact phiT_pos K hx'
    have hR : ∑ e ∈ (DecoSet.dnSet_finite d P hP.ne q).toFinset, phiT K e.1 d'.1 x = 1 := by
      rw [Finset.sum_eq_single_of_mem (⟨e, he⟩ : DecoSet E a ST SG) ((mem_dnFin d ⟨e, he⟩ P hP.ne q).2 hdn) (fun e2 h2 hne =>
        phiT_neg K fun hx2 => hne (Subtype.ext (dn_unique e2.2 he ((mem_dnFin d e2 P hP.ne q).1 h2) hdn hx2 hx)))]
      exact phiT_pos K hx
    rw [hL, hR]
  · rw [Finset.sum_eq_zero fun e' h' => phiT_neg K fun hx => hC (phiMid_of_up d'.2 hP' hq hq2 ((mem_upFin d' e' P q).1 h') hx),
      Finset.sum_eq_zero fun e h' => phiT_neg K fun hx => hC (phiMid_of_dn e.2 d.2 hP hq hq2
        (Deco.IsDn.isUp e.2 d.2 hP hq hq2 ((mem_dnFin d e P hP.ne q).1 h')) hx)]

end Step3

section KI

variable {E : Type} [Field E] [NumberField E] [StarRing E] {K : Type} [Field K] {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

end KI

section AsmG

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end AsmG

section AsmL

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] {a b : ℕ}

end AsmL

section AsmCh

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (hX : X.Ok) (hPr : Pr.Ok) {u : Pr.Word}

end AsmCh

section FrLoc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

def IsFrAt (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (N : Submodule (𝓞 E) (Sp E n)) (f : Sp E n ≃ₗ[E] Sp E n) : Prop :=
  ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P

theorem single_mem_stdAt {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (s : Fin n) : (Pi.single s (1 : E) : Sp E n) ∈ stdAt E n P := by
  unfold stdAt
  rw [mem_localization_standardLattice]
  intro i
  by_cases h : i = s
  · subst h
    rw [Pi.single_eq_same]
    simpa using IntAt.coe P (1 : 𝓞 E)
  · rw [Pi.single_eq_of_ne h]
    simpa using IntAt.coe P (0 : 𝓞 E)

omit [NumberField E] [StarRing E] in
theorem inFr_add (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b) (x y : HomE E a b) : inFr f f' (x + y) = inFr f f' x + inFr f f' y := by
  unfold inFr
  ext v
  simp

end FrLoc

section FrProd

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [StarRing E] {K : Type} [Field K] {a b : ℕ}

theorem intAt_natCast (P : HeightOneSpectrum (𝓞 E)) (k : ℕ) : IntAt P (k : E) := by
  simpa using IntAt.coe P (k : 𝓞 E)

end FrProd

section OffAdmCh

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) {u : Pr.Word}

open Classical in

theorem frsF_isFr {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) : IsFrAt P.1 p.deco.1.N (frsF sel mu p P) := by
  unfold frsF
  by_cases h : P.1 ∈ Pr.vGs
  · rw [dif_pos h]
    exact (Deco.liftFr_spec (p.deco.2.hasLift ⟨P.1, h⟩)).1
  · rw [dif_neg h]
    exact p.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩

theorem qB_dvd (u : Pr.Word) (P : rowSG Pr sel mu) : qOf P.1 ^ cst.B ∣ cBof sel mu cst u :=
  Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun P : rowSG Pr sel mu => qOf P.1) (Finset.mem_univ P)) _) _

end OffAdmCh

section MuMoveP

variable {X : Fields} {n : ℕ}

theorem sel_injective {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} (hsel : IsSel X sel) : Function.Injective sel := by
  intro v v' h
  apply HeightOneSpectrum.ext
  rw [← hsel v, ← hsel v', h]

open Classical in

def muFac (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (v : HeightOneSpectrum (𝓞 X.F)) : X.K :=
  if ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal then 1 else ((mU (sel v) ^ ordDet (sel v) N : X.Kˣ) : X.K)

theorem muOff_eq (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (N : Submodule (𝓞 X.E) (Sp X.E n)) : muOff sel SB mU N = ∏ᶠ v, muFac sel SB mU N v := rfl

open Classical in

def muStep (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (P : HeightOneSpectrum (𝓞 X.E)) (v : HeightOneSpectrum (𝓞 X.F)) : X.K :=
  if ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal then 1
  else ((mU (sel v) ^ (if sel v = P then (-1 : ℤ) else if sel v = conjPrime₂ P then 1 else 0) : X.Kˣ) : X.K)

theorem muFac_support {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} (hsel : IsSel X sel) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (hfin : OrdDetFin X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)) (hN : IsSdLat N) :
    (Function.mulSupport (muFac sel SB mU N)).Finite := by
  refine Set.Finite.subset (Set.Finite.preimage (sel_injective hsel).injOn (hfin N hN)) ?_
  intro v hv
  by_contra hc
  apply hv
  have h0 : ordDet (sel v) N = 0 := by
    by_contra h
    exact hc h
  unfold muFac
  split_ifs
  · rfl
  · rw [h0]
    simp

end MuMoveP

section OrdFin

variable {E : Type} [Field E] [NumberField E]

theorem val_le_one_of_intAt {Q : HeightOneSpectrum (𝓞 E)} {a : E} (h : IntAt Q a) : Q.valuation E a ≤ 1 := by
  obtain ⟨r, s, hs, hrs⟩ := h
  have h1 : Q.valuation E (algebraMap (𝓞 E) E s) = 1 :=
    le_antisymm (Q.valuation_le_one s) (not_lt.1 fun hlt => hs ((Q.valuation_lt_one_iff_mem s).1 hlt))
  have h2 := congrArg (Q.valuation E) hrs
  rw [map_mul, h1, one_mul] at h2
  rw [h2]
  exact Q.valuation_le_one r

theorem ordE_eq_zero {Q : HeightOneSpectrum (𝓞 E)} {a : E} (ha : a ≠ 0) (h : IntAt Q a) (h' : IntAt Q a⁻¹) : ordE Q a = 0 := by
  have h1 := val_le_one_of_intAt h
  have h2 := val_le_one_of_intAt h'
  rw [map_inv₀] at h2
  have h0 : 0 < Q.valuation E a := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ha)
  have h3 : Q.valuation E a = 1 := le_antisymm h1 ((inv_le_one₀ h0).1 h2)
  unfold ordE
  rw [h3, WithZero.log_one, neg_zero]

variable [StarRing E]

theorem frame_det_unit_almost_all_primes (n : ℕ) : OrdDetFin E n := by
  intro N hN
  obtain ⟨a, ha0, ha⟩ := exists_smul_le N (stdLat E n) hN.1.fg (stdLat_lattice (E := E) (n := n)).span_eq_top
  obtain ⟨a', ha0', ha'⟩ := exists_smul_le (stdLat E n) N (stdLat_lattice (E := E) (n := n)).fg hN.1.span_eq_top
  have hI : Ideal.span {a * a'} ≠ (0 : Ideal (𝓞 E)) := by
    intro h0
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h0
    exact (mul_ne_zero ha0 ha0') h0
  refine (Ideal.finite_factors hI).subset ?_
  intro Q hQ
  by_contra hc
  apply hQ
  have hm : a * a' ∉ Q.asIdeal := fun hmem => hc (Ideal.dvd_span_singleton.2 hmem)
  have haQ : a ∉ Q.asIdeal := fun hmem => hm (Ideal.mul_mem_right _ _ hmem)
  have haQ' : a' ∉ Q.asIdeal := fun hmem => hm (Ideal.mul_mem_left _ _ hmem)
  have hloc : localization₂ Q.asIdeal N = stdAt E n Q := SameAt.localization_eq ⟨a, haQ, a', haQ', ha, ha'⟩
  have hspec : ∀ x, frameAt Q N x ∈ localization₂ Q.asIdeal N ↔ x ∈ stdAt E n Q :=
    Classical.epsilon_spec (p := fun f : Sp E n ≃ₗ[E] Sp E n => ∀ x, f x ∈ localization₂ Q.asIdeal N ↔ x ∈ stdAt E n Q)
      ⟨1, fun x => by rw [hloc]; rfl⟩
  have hG : frameAt Q N ∈ GLint E n Q := fun x => by
    have := hspec x
    rw [hloc] at this
    exact this
  exact ordE_eq_zero (Units.ne_zero _) (intAt_det _ hG) (intAt_det_inv _ hG)

end OrdFin

section OrdWD

variable {E : Type} [Field E] [NumberField E]

theorem ordE_mul (Q : HeightOneSpectrum (𝓞 E)) {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) : ordE Q (a * b) = ordE Q a + ordE Q b := by
  unfold ordE
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb)]
  ring

variable [StarRing E]

theorem ordDet_eq_of_frame {n : ℕ} (Q : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (f : Sp E n ≃ₗ[E] Sp E n)
    (hf : ∀ x, f x ∈ localization₂ Q.asIdeal N ↔ x ∈ stdAt E n Q) : ordDet Q N = ordE Q ((LinearEquiv.det f : Eˣ) : E) := by
  have hspec : ∀ x, frameAt Q N x ∈ localization₂ Q.asIdeal N ↔ x ∈ stdAt E n Q :=
    Classical.epsilon_spec (p := fun f : Sp E n ≃ₗ[E] Sp E n => ∀ x, f x ∈ localization₂ Q.asIdeal N ↔ x ∈ stdAt E n Q) ⟨f, hf⟩
  have hG : f⁻¹ * frameAt Q N ∈ GLint E n Q := fun x => by
    rw [← hf]
    show f (f.symm (frameAt Q N x)) ∈ _ ↔ _
    rw [LinearEquiv.apply_symm_apply]
    exact hspec x
  have e : frameAt Q N = f * (f⁻¹ * frameAt Q N) := by rw [mul_inv_cancel_left]
  unfold ordDet
  rw [e, map_mul, Units.val_mul, ordE_mul Q (Units.ne_zero _) (Units.ne_zero _),
    ordE_eq_zero (Units.ne_zero _) (intAt_det _ hG) (intAt_det_inv _ hG), add_zero]

end OrdWD

section MuMoveChP

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

end MuMoveChP

section AsmCh2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (hX : X.Ok) (hPr : Pr.Ok) {u : Pr.Word}

end AsmCh2

section Final

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (hM : MatEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2)) (h1 : Cp1Equiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY)
  (hF : ∀ j, (chF W sel mu L u j).Ok)

end Final

section Tests

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

end Tests

section Final2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (hM : MatEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2)) (h1 : Cp1Equiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY)
  (hF : ∀ j, (chF W sel mu L u j).Ok)

include hPr in
open Classical Formalism.EigenvalueLevelCeiling in

theorem posT_of_mem (hsel : IsSel X sel) (hTp : (Pr.T u).Prime) (hS : Pr.T u ∈ S) : PosT sel mu u := by
  intro P
  have h0 := moveHyp_of_ok hPr u P
  refine ⟨h0.ne, h0.st, fun w => ?_⟩
  rcases Finset.mem_union.mp w.2 with hw | hw
  · exact h0.sg ⟨w.1, hw⟩
  · obtain ⟨v, hv, hvw⟩ := (mem_QE sel mu w.1).mp hw
    have key : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal := by
      intro hi
      rw [← hvw] at hi
      have h1 : ((Pr.T u : ℕ) : 𝓞 X.F) ∈ v.asIdeal := by
        rw [← hsel v]
        show algebraMap (𝓞 X.F) (𝓞 X.E) ((Pr.T u : ℕ) : 𝓞 X.F) ∈ (sel v).asIdeal
        rw [map_natCast]
        exact hi
      have h2 : plc v ∣ Pr.T u := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at h1
        exact (ringChar.spec _ _).mp h1
      have hpp : (plc v).Prime := by
        have : Finite (𝓞 X.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
        have : v.asIdeal.IsPrime := v.isPrime
        exact CharP.char_is_prime (𝓞 X.F ⧸ v.asIdeal) (ringChar (𝓞 X.F ⧸ v.asIdeal))
      have h3 : plc v = Pr.T u := (Nat.prime_dvd_prime_iff_eq hpp hTp).mp h2
      exact (mu.good hv).2.2 (h3 ▸ hS)
    constructor
    · intro hc
      exact key (hc ▸ T_mem hPr u P)
    · intro hc
      apply key
      rw [hc, mem_conjP, map_natCast]
      exact T_mem hPr u P

end Final2

section MoveP

variable {X : Fields} (A : Amb X) {a b : ℕ}

end MoveP

section MoveChP

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

end MoveChP

section Tests2

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] {a b : ℕ}

end Tests2

section MoveCP

variable {X : Fields} (A : Amb X) {a b : ℕ}

end MoveCP

section Cap

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (hM : MatEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2)) (h1 : Cp1Equiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY)
  (hF : ∀ j, (chF W sel mu L u j).Ok)

end Cap

section DiaP

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

end DiaP

section DiaChP

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (hM : MatEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2)) (h1 : Cp1Equiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY)
  (hF : ∀ j, (chF W sel mu L u j).Ok)

end DiaChP

section RedRing

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem intAt_negB {a : E} (h : IntAt P a) : IntAt P (-a) := by
  have := (IntAt.coe P (-1)).mul h
  simpa using this

def intSubB : Subring E where
  carrier := {a | IntAt P a}
  mul_mem' := IntAt.mul
  one_mem' := by
    have := IntAt.coe P 1
    simpa using this
  add_mem' := IntAt.add
  zero_mem' := by
    have := IntAt.coe P 0
    simpa using this
  neg_mem' := intAt_negB P

def redHomB : intSubB P →+* (𝓞 E ⧸ P.asIdeal) where
  toFun a := redP P a.1
  map_one' := by
    have := reduction_coe P 1
    simpa using this
  map_mul' a b := reduction_mul a.2 b.2
  map_zero' := by
    have := reduction_coe P 0
    simpa using this
  map_add' a b := reduction_add a.2 b.2

theorem reduction_det_eq_det_reduction₂ {m : ℕ} (A : Matrix (Fin m) (Fin m) E) (hA : ∀ i j, IntAt P (A i j)) :
    redP P A.det = (Matrix.of fun i j => redP P (A i j)).det := by
  let A' : Matrix (Fin m) (Fin m) (intSubB P) := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have e1 : A = (intSubB P).subtype.mapMatrix A' := by
    ext i j
    rfl
  have e2 : A.det = ((A'.det : intSubB P) : E) := by
    rw [e1, ← RingHom.map_det]
    rfl
  rw [e2]
  show redHomB P A'.det = _
  rw [RingHom.map_det]
  rfl

theorem reduction_det_congr {m : ℕ} (A B : Matrix (Fin m) (Fin m) E) (hA : ∀ i j, IntAt P (A i j)) (hB : ∀ i j, IntAt P (B i j))
    (h : ∀ i j, redP P (A i j) = redP P (B i j)) : redP P A.det = redP P B.det := by
  rw [reduction_det_eq_det_reduction₂ P A hA, reduction_det_eq_det_reduction₂ P B hB]
  congr 1
  ext i j
  exact h i j

theorem intAt_sumB {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i, IntAt P (f i)) : IntAt P (∑ i ∈ s, f i) :=
  (intSubB P).sum_mem fun i _ => hf i

theorem reduction_sum_eq_sum_reduction {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  have h := map_sum (redHomB P) (fun i => (⟨f i, hf i⟩ : intSubB P)) s
  have e : ((∑ i ∈ s, (⟨f i, hf i⟩ : intSubB P) : intSubB P) : E) = ∑ i ∈ s, f i := by
    rw [AddSubmonoidClass.coe_finsetSum]
  rw [← e]
  exact h

variable {P}

structure MCong (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (M M' : ℕ → ℕ → E) : Prop where
  int : ∀ p p', IntAt P (M' p p') ↔ IntAt P (M p p')
  div : ∀ p p', IntAt P (M' p p' / (q : E)) ↔ IntAt P (M p p' / (q : E))
  red : ∀ p p', redP P (M' p p') = redP P (M p p')

theorem mcong_of {q : ℕ} (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal) {M Z : ℕ → ℕ → E} (hZ : ∀ p p', IntAt P (Z p p' / (q : E))) :
    MCong P q M (fun p p' => M p p' + Z p p') := by
  have hqE : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq0
  have hqi : IntAt P (q : E) := by
    have := IntAt.coe P (q : 𝓞 E)
    simpa using this
  have hqr : redP P (q : E) = 0 := by
    have := reduction_coe P (q : 𝓞 E)
    rw [map_natCast] at this
    rw [this]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hq
  have hZe : ∀ p p', Z p p' = (q : E) * (Z p p' / (q : E)) := fun p p' => by
    field_simp
  have hZi : ∀ p p', IntAt P (Z p p') := fun p p' => by
    rw [hZe]
    exact hqi.mul (hZ p p')
  have hZr : ∀ p p', redP P (Z p p') = 0 := fun p p' => by
    rw [hZe, reduction_mul hqi (hZ p p'), hqr, zero_mul]
  have hint : ∀ p p', IntAt P (M p p' + Z p p') ↔ IntAt P (M p p') := fun p p' =>
    ⟨fun h => by
      have := h.add (intAt_negB P (hZi p p'))
      simpa using this, fun h => h.add (hZi p p')⟩
  refine ⟨hint, fun p p' => ?_, fun p p' => ?_⟩
  · show IntAt P ((M p p' + Z p p') / (q : E)) ↔ _
    rw [add_div]
    exact ⟨fun h => by
      have := h.add (intAt_negB P (hZ p p'))
      simpa using this, fun h => h.add (hZ p p')⟩
  · show redP P (M p p' + Z p p') = _
    by_cases h : IntAt P (M p p')
    · rw [reduction_add h (hZi p p'), hZr, add_zero]
    · rw [reduction_eq_zero_of_not_integral P h, reduction_eq_zero_of_not_integral P (mt (hint p p').1 h)]

end RedRing

section Loc1

theorem ite_congrB {α : Type} {c c' : Prop} {i : Decidable c} {i' : Decidable c'} {a a' b : α} (h : c ↔ c') (hv : c' → a = a') :
    @ite α c i a b = @ite α c' i' a' b := by
  by_cases hc : c'
  · rw [if_pos hc, if_pos (h.2 hc), hv hc]
  · rw [if_neg hc, if_neg (mt h.1 hc)]

theorem ite_neB {α : Type} {c : Prop} {i : Decidable c} {a b : α} (h : @ite α c i a b ≠ b) : c := by
  by_contra hc
  exact h (if_neg hc)

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem unitV_congrB (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E} (h : redP P a = redP P b) : LocE.unitV χ a = LocE.unitV χ b := by
  unfold LocE.unitV
  rw [h]

theorem fIdx_zeroB (k₀ n s : ℕ) : LocE.fIdx k₀ 0 n s = s := by
  unfold LocE.fIdx
  split_ifs <;> omega

theorem eN_inB (N p : ℕ) (hp : p < N) : Loc.eN E N p = Pi.single (⟨p, hp⟩ : Fin N) (1 : E) := by
  funext l
  unfold Loc.eN
  by_cases h : l.1 = p
  · have hl : l = ⟨p, hp⟩ := Fin.ext h
    rw [if_pos h, hl, Pi.single_eq_same]
  · have hl : l ≠ ⟨p, hp⟩ := fun e => h (congrArg Fin.val e)
    rw [if_neg h, Pi.single_eq_of_ne hl]

theorem eN_outB (N p : ℕ) (hp : ¬ p < N) : Loc.eN E N p = 0 := by
  funext l
  unfold Loc.eN
  rw [if_neg fun h : l.1 = p => hp (h ▸ l.2)]
  rfl

theorem entB_inB (q k₀ n' n : ℕ) (ex' ex : ℕ → ℕ) (x : HomE E (n' + 0) (n + 0)) {p p' : ℕ} (hp : p < n + 0) (hp' : p' < n' + 0) :
    LocE.entB q k₀ 0 n' 0 n ex' ex x p p' = x (Pi.single ⟨p', hp'⟩ 1) ⟨p, hp⟩ := by
  unfold LocE.entB
  rw [fIdx_zeroB, fIdx_zeroB]
  have s1 : LocE.scE n' ex' p' = 0 := by
    unfold LocE.scE
    rw [if_pos (by omega)]
  have s2 : LocE.scE n ex p = 0 := by
    unfold LocE.scE
    rw [if_pos (by omega)]
  rw [s1, s2, sub_zero, zpow_zero, mul_one, eN_inB _ _ hp']
  unfold Loc.atN
  rw [dif_pos hp]

theorem entB_outB (q k₀ n' n : ℕ) (ex' ex : ℕ → ℕ) (x : HomE E (n' + 0) (n + 0)) {p p' : ℕ} (h : ¬ (p < n + 0 ∧ p' < n' + 0)) :
    LocE.entB q k₀ 0 n' 0 n ex' ex x p p' = 0 := by
  unfold LocE.entB
  rw [fIdx_zeroB, fIdx_zeroB]
  by_cases hp : p < n + 0
  · have hp' : ¬ p' < n' + 0 := fun h' => h ⟨hp, h'⟩
    rw [eN_outB _ _ hp', map_zero]
    unfold Loc.atN
    rw [dif_pos hp]
    simp
  · unfold Loc.atN
    rw [dif_neg hp, zero_mul]

theorem entB_addB (q k₀ n' n : ℕ) (ex' ex : ℕ → ℕ) (x z : HomE E (n' + 0) (n + 0)) :
    LocE.entB q k₀ 0 n' 0 n ex' ex (x + z) = fun p p' => LocE.entB q k₀ 0 n' 0 n ex' ex x p p' + LocE.entB q k₀ 0 n' 0 n ex' ex z p p' := by
  funext p p'
  by_cases h : p < n + 0 ∧ p' < n' + 0
  · rw [entB_inB _ _ _ _ _ _ _ h.1 h.2, entB_inB _ _ _ _ _ _ _ h.1 h.2, entB_inB _ _ _ _ _ _ _ h.1 h.2]
    rfl
  · rw [entB_outB _ _ _ _ _ _ _ h, entB_outB _ _ _ _ _ _ _ h, entB_outB _ _ _ _ _ _ _ h, add_zero]

theorem intAt_zeroB : IntAt P (0 : E) := by
  have := IntAt.coe P 0
  simpa using this

theorem entB_mcongB {q : ℕ} (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal) (k₀ n' n : ℕ) (ex' ex : ℕ → ℕ) (x z : HomE E (n' + 0) (n + 0))
    (hz : ∀ s l, IntAt P ((q : E)⁻¹ * z (Pi.single s 1) l)) :
    MCong P q (LocE.entB q k₀ 0 n' 0 n ex' ex x) (LocE.entB q k₀ 0 n' 0 n ex' ex (x + z)) := by
  rw [entB_addB]
  refine mcong_of hq0 hq fun p p' => ?_
  by_cases h : p < n + 0 ∧ p' < n' + 0
  · rw [entB_inB _ _ _ _ _ _ _ h.1 h.2, div_eq_inv_mul]
    exact hz _ _
  · rw [entB_outB _ _ _ _ _ _ _ h, zero_div]
    exact intAt_zeroB

theorem entB_allIntB (q k₀ n' n a : ℕ) (ha : n' + 0 ≤ a) (ex' ex : ℕ → ℕ) (x : HomE E (n' + 0) (n + 0))
    (h : ∀ p p', p < n + 0 → p' < a → IntAt P (LocE.entB q k₀ 0 n' 0 n ex' ex x p p')) :
    ∀ p p', IntAt P (LocE.entB q k₀ 0 n' 0 n ex' ex x p p') := by
  intro p p'
  by_cases hh : p < n + 0 ∧ p' < n' + 0
  · exact h p p' hh.1 (lt_of_lt_of_le hh.2 ha)
  · rw [entB_outB _ _ _ _ _ _ _ hh]
    exact intAt_zeroB

variable (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

theorem det_congrB {q : ℕ} {M M' : ℕ → ℕ → E} (h : MCong P q M M') (hI : ∀ p p', IntAt P (M p p')) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (m : ℕ) (f g : Fin m → ℕ) :
    LocE.unitV ξ (Matrix.det (Matrix.of fun s s' : Fin m => M' (f s) (g s'))) = LocE.unitV ξ (Matrix.det (Matrix.of fun s s' : Fin m => M (f s) (g s'))) :=
  unitV_congrB ξ (reduction_det_congr P _ _ (fun _ _ => (h.int _ _).2 (hI _ _)) (fun _ _ => hI _ _) fun _ _ => h.red _ _)

theorem lamGv_congrB {q : ℕ} {M M' : ℕ → ℕ → E} (h : MCong P q M M') (hI : ∀ p p', IntAt P (M p p')) (r t j : ℕ) :
    LocE.lamGv ψ₀ χ r t j M' = LocE.lamGv ψ₀ χ r t j M := by
  have hI' : ∀ p p', IntAt P (M' p p') := fun p p' => (h.int p p').2 (hI p p')
  unfold LocE.lamGv
  have e1 : redP P (∑ i ∈ Finset.range (r - 1), M' i (i + 1)) = redP P (∑ i ∈ Finset.range (r - 1), M i (i + 1)) := by
    rw [reduction_sum_eq_sum_reduction P _ _ fun i => hI' _ _, reduction_sum_eq_sum_reduction P _ _ fun i => hI _ _]
    exact Finset.sum_congr rfl fun i _ => h.red _ _
  rw [e1]
  congr 1
  exact Finset.prod_congr rfl fun i _ => det_congrB h hI (χ i) t (fun s => r + i * t + s.1) (fun s => r + i * t + s.1)

theorem lamGvS_congrB {q : ℕ} {M M' : ℕ → ℕ → E} (h : MCong P q M M') (hI : ∀ p p', IntAt P (M p p')) (k₀ r t j : ℕ) :
    LocE.lamGvS ψ₀ χ k₀ r t j M' = LocE.lamGvS ψ₀ χ k₀ r t j M := by
  have hI' : ∀ p p', IntAt P (M' p p') := fun p p' => (h.int p p').2 (hI p p')
  unfold LocE.lamGvS
  have e1 : redP P (∑ i ∈ Finset.range (k₀ - 1), M' i (i + 1) + ∑ i ∈ Finset.range (r - k₀ - 1), M' (k₀ + i) (k₀ + i + 1)) =
      redP P (∑ i ∈ Finset.range (k₀ - 1), M i (i + 1) + ∑ i ∈ Finset.range (r - k₀ - 1), M (k₀ + i) (k₀ + i + 1)) := by
    rw [reduction_add (intAt_sumB P _ _ fun i => hI' _ _) (intAt_sumB P _ _ fun i => hI' _ _),
      reduction_add (intAt_sumB P _ _ fun i => hI _ _) (intAt_sumB P _ _ fun i => hI _ _),
      reduction_sum_eq_sum_reduction P _ _ fun i => hI' _ _, reduction_sum_eq_sum_reduction P _ _ fun i => hI' _ _, reduction_sum_eq_sum_reduction P _ _ fun i => hI _ _, reduction_sum_eq_sum_reduction P _ _ fun i => hI _ _]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => h.red _ _
    · exact Finset.sum_congr rfl fun i _ => h.red _ _
  rw [e1]
  congr 1
  exact Finset.prod_congr rfl fun i _ => det_congrB h hI (χ i) t (fun s => r + i * t + s.1) (fun s => r + i * t + s.1)

theorem phiG_invB {q : ℕ} (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal) (sharp : Bool) (k₀ r t j c' n' n : ℕ) (hc' : c' = 0) (ha : n' + c' ≤ r + (j - 1) * t)
    (x z : HomE E (n' + c') (n + 0)) (hz : ∀ s l, IntAt P ((q : E)⁻¹ * z (Pi.single s 1) l)) :
    LocE.PhiG q ψ₀ χ sharp k₀ r t j c' n' 0 n (x + z) = LocE.PhiG q ψ₀ χ sharp k₀ r t j c' n' 0 n x := by
  subst hc'
  have h := entB_mcongB hq0 hq k₀ n' n (fun i => i + 1) (fun i => i + 1) x z hz
  unfold LocE.PhiG
  dsimp only
  refine ite_congrB ?_ fun hc => ?_
  · simp only [h.int, h.div, h.red]
  · have hI := entB_allIntB q k₀ n' n _ ha _ _ x hc.1
    rw [lamGv_congrB ψ₀ χ h hI, det_congrB h hI (χ (j - 1)) _ (fun s => s.1) (fun s => s.1)]

theorem phiGS_invB {q : ℕ} (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal) (k₀ rS r t j c' n' n : ℕ) (hc' : c' = 0) (ha : n' + c' ≤ r + (j - 1) * t)
    (x z : HomE E (n' + c') (n + 0)) (hz : ∀ s l, IntAt P ((q : E)⁻¹ * z (Pi.single s 1) l)) :
    LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' 0 n (x + z) = LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' 0 n x := by
  subst hc'
  have h := entB_mcongB hq0 hq k₀ n' n (fun i => i + 1) (fun i => i + 1) x z hz
  unfold LocE.PhiGS
  dsimp only
  refine ite_congrB ?_ fun hc => ?_
  · simp only [h.int, h.div, h.red]
  · have hI := entB_allIntB q k₀ n' n _ ha _ _ x hc.1
    rw [lamGvS_congrB ψ₀ χ h hI, det_congrB h hI (χ (j - 1)) _ (fun s => s.1) (fun s => s.1)]

theorem phiQ_invB {q : ℕ} (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' n : ℕ) (hc' : c' = 0)
    (x z : HomE E (n' + c') (n + 0)) (hz : ∀ s l, IntAt P ((q : E)⁻¹ * z (Pi.single s 1) l)) :
    LocE.PhiQ q ξ k₀ r c' n' 0 n (x + z) = LocE.PhiQ q ξ k₀ r c' n' 0 n x := by
  subst hc'
  have h := entB_mcongB hq0 hq k₀ n' n 0 0 x z hz
  unfold LocE.PhiQ
  refine ite_congrB ?_ fun hc => ?_
  · simp only [h.int, h.div]
  · have hI := entB_allIntB q k₀ n' n _ le_rfl _ _ x hc.1
    exact det_congrB h hI ξ _ (fun s => s.1) (fun s => s.1)

theorem phiQ_suppB (q : ℕ) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' n : ℕ) (hc' : c' = 0)
    (x : HomE E (n' + c') (n + 0)) (hx : LocE.PhiQ q ξ k₀ r c' n' 0 n x ≠ 0) : ∀ s l, IntAt P (x (Pi.single s 1) l) := by
  subst hc'
  unfold LocE.PhiQ at hx
  have hc := ite_neB hx
  intro s l
  have := hc.1 l.1 s.1 l.2 s.2
  rwa [entB_inB _ _ _ _ _ _ _ l.2 s.2] at this

end Loc1

section TopLoc

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem cOf_topB {m2 : ℕ} (hm : R.m = m2 + 2) : cOf R (m2 + 1) = 0 := by
  unfold cOf
  omega

theorem cols_topB {m2 : ℕ} (hm : R.m = m2 + 2) : R.N (m2 + 1) + cOf R (m2 + 1) ≤ R.r + (R.m - 1) * R.t := by
  have h1 : (m2 + 1) * (R.t + 1) = (m2 + 1) * R.t + (m2 + 1) := by ring
  have h2 : R.m - 1 = m2 + 1 := by omega
  rw [cOf_topB hm, h2]
  unfold Ranks.N Ranks.r
  omega

theorem qOf_memB (w : HeightOneSpectrum (𝓞 X.E)) : ((qOf w : ℕ) : 𝓞 X.E) ∈ w.asIdeal := Ideal.absNorm_mem _

theorem phiTop_inv {m2 : ℕ} (hm : R.m = m2 + 2) : TopInvAt Ch sel mu cst m2 := by
  intro w y z hz
  unfold PhiTop
  split_ifs with h1 h2
  · exact phiGS_invB _ _ (qOf_pos w.1).ne' (qOf_memB w.1) _ _ _ _ _ _ _ _ (cOf_topB hm) (cols_topB hm) y z hz
  · exact phiG_invB _ _ (qOf_pos w.1).ne' (qOf_memB w.1) _ _ _ _ _ _ _ _ (cOf_topB hm) (cols_topB hm) y z hz
  · exact phiQ_invB (qOf_pos w.1).ne' (qOf_memB w.1) _ _ _ _ _ _ (cOf_topB hm) y z hz

end TopLoc

section Gen3

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem mul_regroup_inv (a c t : E) (ha : a ≠ 0) : c * t = a⁻¹ * c * (a * t) := by
  have e : a⁻¹ * c * (a * t) = c * t * (a * a⁻¹) := by ring
  rw [e, mul_inv_cancel₀ ha, mul_one]

theorem map_stdAt3 {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (B : HomE E a b) (hB : ∀ s l, IntAt P (B (Pi.single s 1) l))
    {v : Sp E a} (hv : v ∈ stdAt E a P) : B v ∈ stdAt E b P := by
  refine (ciMem_stdAt P _).2 fun l => ?_
  exact intAt_linear_form_on_std P ((LinearMap.proj l : Sp E b →ₗ[E] E) ∘ₗ B) (fun s => hB s l) hv

end Gen3

section FtY3

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem intAt_qpow3 (w : HeightOneSpectrum (𝓞 X.E)) (k : ℕ) : IntAt w ((qOf w : X.E) ^ k) := by
  rw [← Nat.cast_pow]
  exact intAt_natCast_kernel_local_factors _ _

theorem fourierTwist_add_integral_of_Q (hcst : cst.Ok) (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D w) {n : ℕ}
    (η ζ : Sp X.E n →ₗ[X.E] X.E) (y : Sp X.E n) (hζ : ∀ i : Fin n, IntAt w.1 (ζ (Pi.single i 1))) (hζy : IntAt w.1 (ζ y))
    (hq : ((qOf w.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n w.1) :
    ftY sel mu cst w (η + ζ) y = ftY sel mu cst w η y := by
  have hqn := intAt_qpow3 (X := X) w.1
  have hiff : (∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * (η + ζ) (Pi.single i 1))) ↔
      ∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * η (Pi.single i 1)) := by
    constructor
    · intro h i
      have h3 := IntAt.add (h i) (intAt_neg_kernel_local_factors ((hqn cst.M).mul (hζ i)))
      have e : (qOf w.1 : X.E) ^ cst.M * (η + ζ) (Pi.single i 1) + -((qOf w.1 : X.E) ^ cst.M * ζ (Pi.single i 1)) =
          (qOf w.1 : X.E) ^ cst.M * η (Pi.single i 1) := by
        rw [LinearMap.add_apply]
        ring
      rwa [e] at h3
    · intro h i
      rw [LinearMap.add_apply, mul_add]
      exact IntAt.add (h i) ((hqn cst.M).mul (hζ i))
  unfold ftY
  rw [if_neg hw, if_neg hw]
  by_cases hI : ∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * η (Pi.single i 1))
  · rw [if_pos (hiff.2 hI), if_pos hI]
    have heps : IntAt w.1 ((epsSg : ℤ) : X.E) := by
      have : ((epsSg : ℤ) : X.E) = -1 := by simp [epsSg]
      rw [this]
      exact intAt_neg_kernel_local_factors (by simpa using intAt_natCast_kernel_local_factors w.1 1)
    have h2 : IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * η y)) := by
      have h3 := intAt_linear_form_on_std w.1 (((qOf w.1 : X.E) ^ cst.M) • η) (fun i => by
        rw [LinearMap.smul_apply, smul_eq_mul]
        exact hI i) hq
      rwa [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at h3
    obtain ⟨k, hk⟩ : ∃ k, cst.D w = k + (cst.M + cst.M) := ⟨cst.D w - 2 * cst.M, by omega⟩
    have hqD : ∀ a : X.E, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * a)) → IntAt w.1 ((qOf w.1 : X.E) ^ cst.D w * a) := by
      intro a ha
      have e : (qOf w.1 : X.E) ^ cst.D w * a = (qOf w.1 : X.E) ^ k * ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * a)) := by
        rw [hk, pow_add, pow_add]
        ring
      rw [e]
      exact (hqn k).mul ha
    rw [LinearMap.add_apply, mul_add, hcst.psi_add w _ _ ?_ ?_, hcst.psi_int w _ (IntAt.mul heps hζy), mul_one]
    · refine hqD _ ?_
      have e : (qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * (((epsSg : ℤ) : X.E) * η y)) =
          ((epsSg : ℤ) : X.E) * ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * η y)) := by ring
      rw [e]
      exact heps.mul h2
    · refine hqD _ ?_
      exact (hqn _).mul ((hqn _).mul (heps.mul hζy))
  · rw [if_neg (mt hiff.1 hI), if_neg hI]

open Classical in

theorem coupling_index_scaled_mem_local {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Y : Set (Sp X.E n)} (hY : Y ∈ ybSet sel mu cst N)
    (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) :
    Y.Nonempty ∧ ∀ a ∈ Y, ((qOf w.1 : X.E) ^ cst.M) • a ∈ localization₂ w.1.asIdeal N := by
  obtain ⟨y0, hy0, rfl⟩ := hY
  refine ⟨⟨y0, ?_⟩, ?_⟩
  · rw [Set.mem_ofPred_eq, sub_self]
    exact zero_mem _
  · intro a ha
    have h1 := (mem_locLat _ _ _ _).1 hy0 w
    simp only [if_neg hw, zpow_neg, zpow_natCast, inv_inv] at h1
    have h2 := (mem_locLat _ _ _ (a - y0)).1 ha w
    simp only [if_neg hw, zpow_natCast] at h2
    have hq0 : (qOf w.1 : X.E) ^ cst.M ≠ 0 := pow_ne_zero _ (by exact_mod_cast (qOf_pos w.1).ne')
    have e : ((qOf w.1 : X.E) ^ cst.M) • a = ((qOf w.1 : X.E) ^ cst.M) • y0 +
        ((qOf w.1 ^ cst.M * qOf w.1 ^ cst.M : ℕ) : X.E) • (((qOf w.1 : X.E) ^ cst.M)⁻¹ • (a - y0)) := by
      rw [smul_smul]
      push_cast
      rw [mul_assoc, mul_inv_cancel₀ hq0, mul_one, smul_sub]
      abel
    rw [e]
    refine add_mem h1 ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem h2 _

end FtY3

section Main3

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word}

theorem modulus_div_prime_pow_integral (w : rowSG Pr sel mu) (b : ℕ) (hb : b ≤ cst.B) :
    IntAt w.1 (((qOf w.1 : X.E) ^ b)⁻¹ * ((cBof sel mu cst u : ℕ) : X.E)) := by
  obtain ⟨kB, hkB⟩ := qB_dvd sel mu cst u w
  obtain ⟨j, hj⟩ : ∃ j, cst.B = b + j := ⟨cst.B - b, by omega⟩
  have hq0 : (qOf w.1 : X.E) ^ b ≠ 0 := pow_ne_zero _ (by exact_mod_cast (qOf_pos w.1).ne')
  have e : ((qOf w.1 : X.E) ^ b)⁻¹ * ((cBof sel mu cst u : ℕ) : X.E) = (qOf w.1 : X.E) ^ j * (kB : X.E) := by
    rw [hkB, hj]
    push_cast
    rw [pow_add, mul_assoc, inv_mul_cancel_left₀ hq0]
  rw [e]
  exact (intAt_qpow3 w.1 j).mul (intAt_natCast_kernel_local_factors _ _)

theorem funLeft_basis_mem_std_lattice (c n : ℕ) (w : HeightOneSpectrum (𝓞 X.E)) (s : Fin (n + c)) :
    LinearMap.funLeft X.E X.E (Fin.castAdd c) (Pi.single s (1 : X.E)) ∈ stdAt X.E n w := by
  refine (ciMem_stdAt w _).2 fun i => ?_
  simp only [LinearMap.funLeft_apply, Pi.single_apply]
  split_ifs
  · simpa using intAt_natCast_kernel_local_factors w 1
  · simpa using intAt_natCast_kernel_local_factors w 0

theorem offCoupling_top_invariance {m2 : ℕ} (h2 : TopInvAt Ch sel mu cst m2) (hPr : Pr.Ok) (hcst : cst.Ok)
    (hDQ : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) (hR : PosT sel mu u)
    (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu) (hYm : Y ∈ ybSet sel mu cst p.deco.1.N)
    (x w0 : HomE X.E (R.N (m2 + 1)) (R.N R.m)) (hw0 : w0 ∈ homAt (rowSG Pr sel mu) p.deco.1.N (tilQ sel mu u d).1.N) :
    offCpl2 Ch sel mu cst m2 p Y d (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w0) = offCpl2 Ch sel mu cst m2 p Y d x := by
  have hTc : ∀ Q : Pr.vT u, cO X.E (Pr.piT u) ∉ Q.1.asIdeal := conj_piT_notMem hPr u
  have hGc : ∀ w : rowSG Pr sel mu, Pr.piT u ∉ w.1.asIdeal := fun w hw =>
    ((hR ⟨w.1, (mem_divs (hPr.piT_ne_zero u) w.1).2 hw⟩).sg w).1 rfl
  have hfr := frsF_isFr sel mu p
  unfold offCpl2
  refine Finset.prod_congr rfl fun w _ => ?_
  have hgr : ∀ v, d.1.liftFr w v ∈ localization₂ w.1.asIdeal d.1.N ↔ v ∈ stdAt X.E (R.N R.m - 1) w.1 :=
    (Deco.liftFr_spec (d.2.hasLift w)).1
  have hpi : IntAt w.1 (((Pr.piT u : 𝓞 X.E) : X.E))⁻¹ := by
    have := IntAt.div_of_notMem (intAt_natCast_kernel_local_factors w.1 1) (hGc w)
    simpa using this
  have hW : ∀ v : Sp X.E (R.N (m2 + 1)), v ∈ stdAt X.E (R.N (m2 + 1)) w.1 →
      (d.1.liftFr w).symm (prXp X.E R (w0 (frsF sel mu p w v))) ∈ stdAt X.E (R.N R.m - 1) w.1 ∧
        IntAt w.1 (atNL X.E (R.N R.m) (R.N R.m - 1) (w0 (frsF sel mu p w v))) := by
    intro v hv
    have h1' : frsF sel mu p w v ∈ localization₂ w.1.asIdeal p.deco.1.N := (hfr w v).2 hv
    have h2' : w0 (frsF sel mu p w v) ∈ localization₂ w.1.asIdeal (tilQ sel mu u d).1.N := hw0 w.1 w.2 _ h1'
    have h3 := tilde_lattice_restrict_mem (N_m_succ R) (ST := Pr.vT u) (Pr.piT u) d hTc hGc
      (fun i : Fin ((R.N R.m - 1) + 0) => (⟨i.1, by have := i.2; omega⟩ : Fin (R.N R.m))) (fun _ => rfl) w.1 _ h2'
    refine ⟨?_, h3.2⟩
    apply (hgr _).1
    rw [LinearEquiv.apply_symm_apply]
    exact h3.1
  congr 1
  · simp only [LinearMap.add_comp, LinearMap.comp_add]
    refine h2 w _ _ fun s l => ?_
    have e2 : ((d.1.liftFr w).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ (((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w0) ∘ₗ
        (frsF sel mu p w).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) (Pi.single s 1) l =
        ((cBof sel mu cst u : ℕ) : X.E) * ((d.1.liftFr w).symm (prXp X.E R (w0 (frsF sel mu p w
          (LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Pi.single s 1)))))) l := by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply]
      rw [← algebraMap_smul X.E (((cBof sel mu cst u : ℕ) : 𝓞 X.E)), map_smul, map_smul, Pi.smul_apply, smul_eq_mul, map_natCast]
    rw [e2, ← mul_assoc]
    have h4 := modulus_div_prime_pow_integral sel mu cst (u := u) w 1 hcst.B_pos
    rw [pow_one] at h4
    exact h4.mul ((ciMem_stdAt w.1 _).1 (hW _ (funLeft_basis_mem_std_lattice _ _ w.1 s)).1 l)
  · simp only [LinearMap.add_comp, LinearMap.comp_add]
    have hζ : ∀ b : ℕ, b ≤ cst.B → ∀ v : Sp X.E (R.N (m2 + 1)), ((qOf w.1 : X.E) ^ b) • v ∈ stdAt X.E (R.N (m2 + 1)) w.1 →
        IntAt w.1 (((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ
          (((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w0) ∘ₗ (frsF sel mu p w).toLinearMap) v) := by
      intro b hb v hv
      have hI := (hW _ hv).2
      have hq0 : (qOf w.1 : X.E) ^ b ≠ 0 := pow_ne_zero _ (by exact_mod_cast (qOf_pos w.1).ne')
      have e3 : atNL X.E (R.N R.m) (R.N R.m - 1) (w0 (frsF sel mu p w (((qOf w.1 : X.E) ^ b) • v))) =
          (qOf w.1 : X.E) ^ b * atNL X.E (R.N R.m) (R.N R.m - 1) (w0 (frsF sel mu p w v)) := by
        rw [map_smul, map_smul, map_smul, smul_eq_mul]
      rw [e3] at hI
      have e4 : ((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ
          (((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w0) ∘ₗ (frsF sel mu p w).toLinearMap) v =
          (((Pr.piT u : 𝓞 X.E) : X.E))⁻¹ * ((((qOf w.1 : X.E) ^ b)⁻¹ * ((cBof sel mu cst u : ℕ) : X.E)) *
            ((qOf w.1 : X.E) ^ b * atNL X.E (R.N R.m) (R.N R.m - 1) (w0 (frsF sel mu p w v)))) := by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply, smul_eq_mul]
        rw [← algebraMap_smul X.E (((cBof sel mu cst u : ℕ) : 𝓞 X.E)), map_smul, smul_eq_mul, map_natCast]
        congr 1
        exact mul_regroup_inv _ _ _ hq0
      rw [e4]
      exact hpi.mul ((modulus_div_prime_pow_integral sel mu cst (u := u) w b hb).mul hI)
    have hs : ∀ i : Fin (R.N (m2 + 1)), ((qOf w.1 : X.E) ^ 0) • (Pi.single i (1 : X.E) : Sp X.E (R.N (m2 + 1))) ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
      intro i
      rw [pow_zero, one_smul]
      exact ciSingle_mem i
    by_cases hw : w.1 ∈ Pr.vGs
    · obtain ⟨hne, -, hqm⟩ := ybSet_props2 sel mu cst hYm w hw
      have hq : ((qOf w.1 : ℕ) : X.E) • (frsF sel mu p w).symm (repY Y) ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
        rw [← LinearEquiv.map_smul]
        apply (hfr w _).1
        rw [LinearEquiv.apply_symm_apply]
        exact hqm _ (representative_mem hne)
      refine fourierTwist_add_integral sel mu cst hcst w hw _ _ _ (fun i => hζ 0 (Nat.zero_le _) _ (hs i)) (hζ 1 hcst.B_pos _ ?_) hq
      rw [pow_one]
      exact hq
    · obtain ⟨hne, hqm⟩ := coupling_index_scaled_mem_local sel mu cst hYm w hw
      have hq : ((qOf w.1 : X.E) ^ cst.M) • (frsF sel mu p w).symm (repY Y) ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
        rw [← LinearEquiv.map_smul]
        apply (hfr w _).1
        rw [LinearEquiv.apply_symm_apply]
        exact hqm _ (representative_mem hne)
      exact fourierTwist_add_integral_of_Q sel mu cst hcst w hw (hDQ w hw) _ _ _ (fun i => hζ 0 (Nat.zero_le _) _ (hs i)) (hζ cst.M hcst.M_le_B _ hq) hq

end Main3

section Cap2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (hM : MatEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2)) (h1 : Cp1Equiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY)
  (hF : ∀ j, (chF W sel mu L u j).Ok)

end Cap2

section Rk1C

variable {E : Type} [Field E] {n : ℕ}

def rk1C (lam : Sp E n →ₗ[E] E) (v : Sp E n) (c : E) : Sp E n →ₗ[E] Sp E n := LinearMap.id + ((c - 1) • lam).smulRight v

theorem rankOneScaling_apply (lam : Sp E n →ₗ[E] E) (v : Sp E n) (c : E) (y : Sp E n) : rk1C lam v c y = y + ((c - 1) * lam y) • v := by
  simp [rk1C]

theorem rankOneScaling_one (lam : Sp E n →ₗ[E] E) (v : Sp E n) : rk1C lam v 1 = LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  rw [rankOneScaling_apply, sub_self, zero_mul, zero_smul, add_zero]
  rfl

theorem rankOneScaling_comp (lam : Sp E n →ₗ[E] E) (v : Sp E n) (hv : lam v = 1) (c c' : E) : rk1C lam v c ∘ₗ rk1C lam v c' = rk1C lam v (c * c') := by
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.comp_apply, rankOneScaling_apply lam v c', rankOneScaling_apply lam v c, rankOneScaling_apply lam v (c * c'), map_add, map_smul, hv, smul_eq_mul, mul_one,
    add_assoc, ← add_smul]
  refine congrArg (fun t => y + t • v) ?_
  ring

def rk1EC (lam : Sp E n →ₗ[E] E) (v : Sp E n) (hv : lam v = 1) (c : E) (hc : c ≠ 0) : Sp E n ≃ₗ[E] Sp E n :=
  LinearEquiv.ofLinearMap (rk1C lam v c) (rk1C lam v c⁻¹) (by rw [rankOneScaling_comp lam v hv, mul_inv_cancel₀ hc, rankOneScaling_one])
    (by rw [rankOneScaling_comp lam v hv, inv_mul_cancel₀ hc, rankOneScaling_one])

end Rk1C

section OrdC

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

variable {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end OrdC

section OrdD

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem intAt_smul_locPD (Q : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)} {c : E} (hc : IntAt Q c) {z : Sp E n}
    (hz : z ∈ localization₂ Q.asIdeal N) : c • z ∈ localization₂ Q.asIdeal N := by
  obtain ⟨r, s, hs, hrs⟩ := hc
  obtain ⟨s', hs', hz'⟩ := (mem_locP Q N z).1 hz
  refine (mem_locP Q N _).2 ⟨s * s', fun h => (Q.isPrime.mem_or_mem h).elim hs hs', ?_⟩
  have e : (s * s') • (c • z) = r • (s' • z) := by
    rw [← algebraMap_smul E (s * s'), ← algebraMap_smul E r, ← algebraMap_smul E s' z, smul_smul, smul_smul, map_mul, ← hrs]
    congr 1
    ring
  rw [e]
  exact N.smul_mem r hz'

theorem exists_frameD (Q : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) :
    ∃ f : Sp E n ≃ₗ[E] Sp E n, IsFrAt Q N f := by
  obtain ⟨β, hβ, hint⟩ := exists_locBasis Q hN
  refine ⟨β.equivFun.symm, fun y => ⟨fun h => (ciMem_stdAt Q y).2 fun i => ?_, fun h => ?_⟩⟩
  · have h2 := hint _ h i
    have e := congrFun (β.equivFun.apply_symm_apply y) i
    rw [Module.Basis.equivFun_apply] at e
    rwa [e] at h2
  · rw [Module.Basis.equivFun_symm_apply]
    exact Submodule.sum_mem _ fun i _ => intAt_smul_locPD Q ((ciMem_stdAt Q y).1 h i) (hβ i)

def rk1D (lam : Sp E n →ₗ[E] E) (v : Sp E n) (c : E) : Sp E n →ₗ[E] Sp E n := LinearMap.id + (c - 1) • lam.smulRight v

theorem rankOneDilation_apply (lam : Sp E n →ₗ[E] E) (v : Sp E n) (c : E) (y : Sp E n) : rk1D lam v c y = y + ((c - 1) * lam y) • v := by
  simp [rk1D, smul_smul]

theorem lam_rk1D (lam : Sp E n →ₗ[E] E) (v : Sp E n) (h1 : lam v = 1) (c : E) (y : Sp E n) : lam (rk1D lam v c y) = c * lam y := by
  rw [rankOneDilation_apply, map_add, map_smul, h1, smul_eq_mul]
  ring

theorem rankOneDilation_comp (lam : Sp E n →ₗ[E] E) (v : Sp E n) (h1 : lam v = 1) (c c' : E) :
    rk1D lam v c ∘ₗ rk1D lam v c' = rk1D lam v (c * c') := by
  ext1 y
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply]
  rw [rankOneDilation_apply lam v c, lam_rk1D lam v h1, rankOneDilation_apply, rankOneDilation_apply, add_assoc, ← add_smul]
  congr 2
  ring

theorem rankOneDilation_one (lam : Sp E n →ₗ[E] E) (v : Sp E n) : rk1D lam v 1 = LinearMap.id := by
  simp [rk1D]

def rk1ED (lam : Sp E n →ₗ[E] E) (v : Sp E n) (h1 : lam v = 1) (c : E) (hc : c ≠ 0) : Sp E n ≃ₗ[E] Sp E n :=
  LinearEquiv.ofLinearMap (rk1D lam v c) (rk1D lam v c⁻¹)
    (by rw [rankOneDilation_comp lam v h1, mul_inv_cancel₀ hc, rankOneDilation_one]) (by rw [rankOneDilation_comp lam v h1, inv_mul_cancel₀ hc, rankOneDilation_one])

end OrdD

section OrdD2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end OrdD2

section OrdUpP

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end OrdUpP

section Cap3

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (hM : MatEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2)) (h1 : Cp1Equiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY)
  (hF : ∀ j, (chF W sel mu L u j).Ok)

end Cap3

end Formalism.L2.Ker
