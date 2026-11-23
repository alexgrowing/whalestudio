import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.ChainInst
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Lift

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.IsLift (d : Deco E n ST SG) (w : SG) (f : Sp E n ≃ₗ[E] Sp E n) : Prop :=
  (∀ x, f x ∈ d.at w.1 ↔ x ∈ stdAt E n w.1) ∧ ∀ x ∈ stdAt E n w.1, d.be w (f x) = redV w.1 x

def Deco.HasLift (d : Deco E n ST SG) (w : SG) : Prop := ∃ f, d.IsLift w f

theorem Deco.liftFr_spec {d : Deco E n ST SG} {w : SG} (h : d.HasLift w) : d.IsLift w (d.liftFr w) := Classical.epsilon_spec (p := fun f => d.IsLift w f) h

end Lift

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

open Classical in

def PhiTopG (sharp : Bool) (i j n : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : Loc.SF X.E X.K (R.N i + cOf R i) ((n - 1) + 0) :=
  if P ∈ Pr.vGs then
    (if sharp then LocE.PhiGS (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.rS R.r R.t j (cOf R i) (R.N i) 0 (n - 1)
      else LocE.PhiG (qOf P) (psi0P Ch P) (chiP Ch P) false R.k R.r R.t j (cOf R i) (R.N i) 0 (n - 1))
  else LocE.PhiQ (qOf P) (resChar (mu : Chr X.F X.E X.K) P) R.k R.r (cOf R i) (R.N i) 0 (n - 1)

def prXpG (E : Type) [Field E] (n : ℕ) : Sp E n →ₗ[E] Sp E ((n - 1) + 0) :=
  LinearMap.funLeft E E fun i : Fin ((n - 1) + 0) => (⟨i.1, by have := i.2; omega⟩ : Fin n)

open Classical in

def frsG {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 X.E))} (p : DecoF X.E n ST Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) :
    Frs X.E n (rowSG Pr sel mu) := fun P =>
  if h : P.1 ∈ Pr.vGs then p.deco.1.liftFr ⟨P.1, h⟩ else p.fr ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩

def XiTopG {u : Pr.Word} (i j n : ℕ) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : DecoF X.E n (Pr.vT u) Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (x : HomE X.E (R.N i) n) : X.K :=
  phiT X.K p.deco.1 p'.deco.1 x *
    ∏ P : rowSG Pr sel mu,
      PhiTopG Ch mu cst.sharp i j n P.1 (prXpG X.E n ∘ₗ inFr (frsF sel mu p P) (frsG sel mu p' P) x ∘ₗ
          LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R i))) *
        ftY sel mu cst P (atNL X.E n (n - 1) ∘ₗ inFr (frsF sel mu p P) (frsG sel mu p' P) x) ((frsF sel mu p P).symm (repY Y))

def XiTop {u : Pr.Word} (i : ℕ) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i))) (p' : ChPt (R := R) sel mu u (i + 1))
    (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  XiTopG Ch sel mu cst i (i + 1) (R.N (i + 1)) p Y p' x

variable {u : Pr.Word} {m2 : ℕ} (T : ChTh W sel mu u m2)

open Classical in

def cpTopK (i : ℕ) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i))) (p' : ChPt (R := R) sel mu u (i + 1)) :
    (colValF W sel mu u i).V →ₗ[X.K] (colValF W sel mu u (i + 1)).V :=
  if Y ∈ ybSet sel mu cst p.deco.1.N then
    kerOf (T.th i) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p)
      p'.deco.1.N (frsF sel mu p') (XiTop Ch sel mu cst i p Y p')
  else 0

end Top

section LiftEx

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem Deco.Ok.be_zero {d : Deco E n ST SG} (hd : d.Ok) (w : SG) : d.be w 0 = 0 := by
  simpa using hd.be_smul w 0 0 (Submodule.zero_mem _)

theorem Deco.Ok.be_sum {d : Deco E n ST SG} (hd : d.Ok) (w : SG) {ι : Type} (s : Finset ι) (g : ι → Sp E n)
    (hg : ∀ i ∈ s, g i ∈ d.at w.1) : d.be w (∑ i ∈ s, g i) = ∑ i ∈ s, d.be w (g i) := by
  classical
  revert hg
  refine Finset.induction_on s (fun _ => by simp [hd.be_zero w]) ?_
  intro a s ha ih hg
  rw [Finset.sum_insert ha, Finset.sum_insert ha,
    hd.be_add w _ (hg a (Finset.mem_insert_self a s)) _
      (Submodule.sum_mem _ fun i hi => hg i (Finset.mem_insert_of_mem hi)),
    ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

private theorem mk_mul_reduction_eq_mk {P : HeightOneSpectrum (𝓞 E)} {a : E} {r s : 𝓞 E} (hs : s ∉ P.asIdeal)
    (hrs : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r) :
    Ideal.Quotient.mk P.asIdeal s * redP P a = Ideal.Quotient.mk P.asIdeal r := by
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hs0
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧
      algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨b * Ideal.Quotient.mk P.asIdeal r, r, s, hs, hrs, by rw [← mul_assoc, hb, one_mul]⟩
  unfold redP
  rw [dif_pos hex]
  obtain ⟨r', s', hs', hrs', hc⟩ := hex.choose_spec
  have key : s * r' = s' * r := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [map_mul, map_mul, ← hrs', ← hrs]
    ring
  have hs0' : Ideal.Quotient.mk P.asIdeal s' ≠ 0 := fun h0 => hs' (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  apply mul_left_cancel₀ hs0'
  rw [← mul_assoc, mul_comm (Ideal.Quotient.mk P.asIdeal s'), mul_assoc, hc,
    ← map_mul (Ideal.Quotient.mk P.asIdeal) s r', key, map_mul]

theorem yIntAt_inv {P : HeightOneSpectrum (𝓞 E)} {a : E} (ha : IntAt P a) (h : redP P a ≠ 0) : IntAt P a⁻¹ := by
  haveI : P.asIdeal.IsPrime := P.isPrime
  obtain ⟨r, s, hs, hrs⟩ := ha
  have hr : r ∉ P.asIdeal := by
    intro hr
    apply h
    have h1 := mk_mul_reduction_eq_mk hs hrs
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr] at h1
    have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    exact (mul_eq_zero.mp h1).resolve_left hs0
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hr
    have : r = 0 := IsFractionRing.injective (𝓞 E) E (by rw [map_zero, ← hrs, mul_zero])
    rw [this]
    exact Ideal.zero_mem _
  unfold IntAt
  exact ⟨s, r, hr, by rw [← hrs, mul_assoc, mul_inv_cancel₀ ha0, mul_one]⟩

theorem yInt_smul_mem {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} {a : E} (ha : IntAt P a) {x : Sp E n}
    (hx : x ∈ localization₂ P.asIdeal N) : a • x ∈ localization₂ P.asIdeal N := by
  obtain ⟨r, s, hs, hrs⟩ := ha
  have hx' : ∃ t ∈ P.asIdeal.primeCompl, t • x ∈ N := hx
  obtain ⟨t, ht, htx⟩ := hx'
  show ∃ t ∈ P.asIdeal.primeCompl, t • (a • x) ∈ N
  refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
  have e : (s * t) • (a • x) = r • (t • x) := by
    rw [← algebraMap_smul E (s * t), smul_smul, ← algebraMap_smul E r, ← algebraMap_smul E t, smul_smul]
    congr 1
    rw [map_mul]
    linear_combination (algebraMap (𝓞 E) E t) * hrs
  rw [e]
  exact N.smul_mem r htx

theorem Deco.Ok.be_int_smul {d : Deco E n ST SG} (hd : d.Ok) (w : SG) {a : E} (ha : IntAt w.1 a) {x : Sp E n} (hx : x ∈ d.at w.1) :
    d.be w (a • x) = redP w.1 a • d.be w x := by
  haveI : w.1.asIdeal.IsPrime := w.1.isPrime
  have hax : a • x ∈ d.at w.1 := yInt_smul_mem ha hx
  obtain ⟨r, s, hs, hrs⟩ := ha
  have e : s • (a • x) = r • x := by
    rw [← algebraMap_smul E s, smul_smul, ← algebraMap_smul E r, hrs]
  have h1 := hd.be_smul w s (a • x) hax
  rw [e, hd.be_smul w r x hx] at h1
  have hsp := mk_mul_reduction_eq_mk (P := w.1) hs hrs
  have hs0 : Ideal.Quotient.mk w.1.asIdeal s ≠ 0 := fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  apply smul_right_injective (Fin n → 𝓞 E ⧸ w.1.asIdeal) hs0
  dsimp only
  rw [← h1, smul_smul, hsp]

theorem Deco.Ok.hasLift {d : Deco E n ST SG} (hd : d.Ok) (w : SG) : d.HasLift w := by
  classical
  haveI : w.1.asIdeal.IsPrime := w.1.isPrime
  choose y hyN hyb using fun i : Fin n => hd.be_surj w (Pi.single i 1)
  have hNat : ∀ z ∈ d.N, z ∈ d.at w.1 := fun z hz => by
    show ∃ t ∈ w.1.asIdeal.primeCompl, t • z ∈ d.N
    exact ⟨1, w.1.asIdeal.primeCompl.one_mem, by rwa [one_smul]⟩
  have hat : ∀ z : Sp E n, z ∈ d.at w.1 ↔ ∃ t : 𝓞 E, t ∉ w.1.asIdeal ∧ t • z ∈ d.N := by
    intro z
    show (∃ t ∈ w.1.asIdeal.primeCompl, t • z ∈ d.N) ↔ _
    simp only [Ideal.mem_primeCompl_iff]
  have hstd : ∀ x : Sp E n, x ∈ stdAt E n w.1 ↔ ∃ t : 𝓞 E, t ∉ w.1.asIdeal ∧
      ∃ b : Fin n → 𝓞 E, ∀ i, algebraMap (𝓞 E) E (b i) = algebraMap (𝓞 E) E t * x i := by
    intro x
    show (∃ t ∈ w.1.asIdeal.primeCompl, t • x ∈ stdLat E n) ↔ _
    simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, forall_const, Submodule.mem_one,
      Pi.smul_apply, Algebra.smul_def, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨t, ht, h⟩
      choose b hb using h
      exact ⟨t, ht, b, hb⟩
    · rintro ⟨t, ht, b, hb⟩
      exact ⟨t, ht, fun i => ⟨b i, hb i⟩⟩
  let g : Sp E n →ₗ[E] Sp E n :=
    { toFun := fun x => ∑ i, x i • y i
      map_add' := fun x x' => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum] }
  have hg : ∀ x, g x = ∑ i, x i • y i := fun x => rfl
  let L : Submodule (𝓞 E) (Sp E n) := Submodule.span (𝓞 E) (Set.range y)
  have hneg : ∀ v ∈ d.at w.1, d.be w (-v) = -d.be w v := fun v hv => by
    simpa using hd.be_smul w (-1) v hv
  have hN1 : d.N ≤ L ⊔ w.1.asIdeal • d.N := by
    intro z hz
    choose a ha using fun i => Ideal.Quotient.mk_surjective (I := w.1.asIdeal) (d.be w z i)
    have hsN : (∑ i, a i • y i) ∈ d.N := Submodule.sum_mem _ fun i _ => d.N.smul_mem _ (hyN i)
    have hL : (∑ i, a i • y i) ∈ L :=
      Submodule.sum_mem _ fun i _ => L.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    have hbe : d.be w (∑ i, a i • y i) = d.be w z := by
      rw [hd.be_sum w _ _ (fun i _ => hNat _ (d.N.smul_mem _ (hyN i)))]
      have e : ∀ i, d.be w (a i • y i) = Ideal.Quotient.mk w.1.asIdeal (a i) • Pi.single i 1 := fun i => by
        rw [hd.be_smul w _ _ (hNat _ (hyN i)), hyb]
      simp only [e]
      funext j
      simp [Finset.sum_apply, Pi.single_apply, ha]
    have hker : z - ∑ i, a i • y i ∈ w.1.asIdeal • d.N := by
      refine hd.be_ker w _ (d.N.sub_mem hz hsN) ?_
      rw [sub_eq_add_neg, hd.be_add w _ (hNat _ hz) _ (hNat _ (d.N.neg_mem hsN)), hneg _ (hNat _ hsN), hbe]
      simp
    exact Submodule.mem_sup.mpr ⟨_, hL, _, hker, by abel⟩
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul w.1.asIdeal
    (d.N.map L.mkQ) (hd.lat.fg.map _) (by
      calc d.N.map L.mkQ ≤ (L ⊔ w.1.asIdeal • d.N).map L.mkQ := Submodule.map_mono hN1
        _ = w.1.asIdeal • d.N.map L.mkQ := by
          rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_smul''])
  have hrN : ∀ z ∈ d.N, r • z ∈ L := fun z hz => by
    have h0 := hr (L.mkQ z) (Submodule.mem_map_of_mem hz)
    rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  have hrP : r ∉ w.1.asIdeal := fun h =>
    w.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using w.1.asIdeal.sub_mem h hr1))
  have hr0 : algebraMap (𝓞 E) E r ≠ 0 := fun h0 => hrP (by
    have : r = 0 := IsFractionRing.injective (𝓞 E) E (by rw [h0, map_zero])
    rw [this]
    exact Ideal.zero_mem _)
  have hLg : ∀ v ∈ L, ∃ c : Fin n → 𝓞 E, v = g (fun i => algebraMap (𝓞 E) E (c i)) := fun v hv => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := 𝓞 E)).mp hv
    refine ⟨c, ?_⟩
    rw [hg, ← hc]
    simp only [algebraMap_smul]
  have hNg : ∀ z ∈ d.N, ∃ c : Fin n → 𝓞 E,
      z = g ((algebraMap (𝓞 E) E r)⁻¹ • fun i => algebraMap (𝓞 E) E (c i)) := fun z hz => by
    obtain ⟨c, hc⟩ := hLg _ (hrN z hz)
    refine ⟨c, ?_⟩
    rw [map_smul, ← hc, ← algebraMap_smul E r z, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  have hsurj : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hd.lat.span_eq_top, Submodule.span_le]
    intro z hz
    obtain ⟨c, hc⟩ := hNg z hz
    exact LinearMap.mem_range.mpr ⟨_, hc.symm⟩
  have hinj : Function.Injective g := LinearMap.injective_iff_surjective.mpr hsurj
  refine ⟨LinearEquiv.ofBijective g ⟨hinj, hsurj⟩, fun x => ?_, fun x hx => ?_⟩
  · show g x ∈ d.at w.1 ↔ x ∈ stdAt E n w.1
    constructor
    · intro hgx
      obtain ⟨t, ht, htN⟩ := (hat _).mp hgx
      rw [← LinearMap.map_smul_of_tower g t x] at htN
      obtain ⟨c, hc⟩ := hNg _ htN
      have e := hinj hc
      refine (hstd x).mpr ⟨r * t, fun h => (w.1.isPrime.mem_or_mem h).elim hrP ht, c, fun i => ?_⟩
      have hi := congr_fun e i
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def] at hi
      rw [map_mul, mul_assoc, hi, ← mul_assoc, mul_inv_cancel₀ hr0, one_mul]
    · intro hx
      obtain ⟨t, ht, b, hb⟩ := (hstd x).mp hx
      refine (hat _).mpr ⟨t, ht, ?_⟩
      have e : t • x = fun i => algebraMap (𝓞 E) E (b i) := by
        funext i
        rw [Pi.smul_apply, Algebra.smul_def, hb]
      rw [← LinearMap.map_smul_of_tower g t x, hg, e]
      exact Submodule.sum_mem _ fun i _ => by
        simp only [algebraMap_smul]
        exact d.N.smul_mem _ (hyN i)
  · show d.be w (g x) = redV w.1 x
    rw [hg]
    obtain ⟨t, ht, b, hb⟩ := (hstd x).mp hx
    have hint : ∀ i, IntAt w.1 (x i) := fun i => ⟨b i, t, ht, (hb i).symm⟩
    rw [hd.be_sum w _ _ (fun i _ => yInt_smul_mem (hint i) (hNat _ (hyN i)))]
    have e : ∀ i, d.be w (x i • y i) = redP w.1 (x i) • Pi.single i 1 := fun i => by
      rw [hd.be_int_smul w (hint i) (hNat _ (hyN i)), hyb]
    simp only [e]
    funext j
    simp [Finset.sum_apply, Pi.single_apply, redV]

end LiftEx

section Cmp

open Formalism.L2.Ker

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

theorem PhiTopG_eq (sharp : Bool) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) :
    PhiTopG Ch mu sharp (m2 + 1) R.m (R.N R.m) P = PhiTop Ch mu sharp m2 P := rfl

theorem frsG_eq {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) : frsG sel mu p = frsF sel mu p := rfl

open Classical in

def cpTopM {u : Pr.Word} {m2 : ℕ} (T : ChTh W sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    (p' : DecoF X.E (R.N R.m) (Pr.vT u) Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) :
    (colValF W sel mu u (m2 + 1)).V →ₗ[X.K] (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).V :=
  if Y ∈ ybSet sel mu cst p.deco.1.N then
    kerOf T.top (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p)
      p'.deco.1.N (frsG sel mu p') (XiTopG Ch sel mu cst (m2 + 1) R.m (R.N R.m) p Y p')
  else 0

def XiTopTil (m2 : ℕ) (u : Pr.Word) : Prop :=
  ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu)
    (p' : DecoF X.E (R.N R.m) (Pr.vT u) Pr.vGs (QE sel (mu : Chr X.F X.E X.K))), p'.deco = tilC sel mu u d →
    Y ∈ ybSet sel mu cst p.deco.1.N →
      XiTopG Ch sel mu cst (m2 + 1) R.m (R.N R.m) p Y p' = XiCpl2 Ch sel mu cst m2 p Y d

end Cmp

def XiTopTilRef : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ) (u : Pr.Word), X.Ok → Pr.Ok → cst.Ok →
    R.m = m2 + 2 → (∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs) → (∀ w : Pr.vGs, Pr.piT u ∉ w.1.asIdeal) → XiTopTil Ch sel mu cst m2 u

end Formalism.L2.Col
