import Formalism.SharpRestriction.LevelLetterCocycles.JumpsLetOfWin
import Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor
import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.Split

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def SplitLift : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ A : ArcP n, A.OK →
  ∀ (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L),
    Win W A T₂ → IsCrys PD Y.ρ → IsSESLat (Qp := Qp) ι π →
    ∀ rr : ℕ, (∀ c ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W π c (Formalism.MainNotions.LiftingTheory.lp W rr)) →
    ∀ e : W.DD W.one, e ∈ W.N W.one → W.N W.one = Submodule.span (LetA O n) {e} →
      W.φD W.one e = e → (∀ g, W.γD W.one g e = e) → ∀ b : O,
    ∃ (xt : W.DD Y) (y z : W.DD T₂) (w τ : ZMod n → W.DD T₂),
      (∀ δ ∈ W.DelF, W.γD Y δ xt = xt) ∧
      W.map π xt = (b * ((PD.p : ℕ) : O) ^ (rr + A.σ PD.p)) • e ∧
      W.map ι y = W.φD Y xt - xt ∧ W.map ι z = W.γ Y xt - xt ∧
      (y, z) ∈ W.wachCocyclesDelta T₂ ∧ InFN W T₂ (W.π₀ ^ A.M PD.p) z ∧
      (∀ c ∈ A.cuts, InI W T₂ c (w c) ∧
        InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1 (abelian₂ W A c (A.len c) • w c) ∧
        IsTr W A T₂ c (w c) (τ c) ∧
        ∃ p ∈ Pp W Y (c - ((A.len c : ℕ) : ZMod n)) (A.len c), ∃ x ∈ W.Nl Y c, W.map ι (w c) = p - x) ∧
      ∑ c ∈ A.cuts, (lA W ^ A.σ PD.p • ((W.φD T₂) ^ A.j) (w c) - τ c) = lA W ^ A.σ PD.p • y

def SplitShape : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ A : ArcP n, A.OK →
  ∀ (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L),
    Win W A T₂ → IsCrys PD Y.ρ → IsSESLat (Qp := Qp) ι π → ∀ c ∈ A.cuts, ∀ w : W.DD T₂,
    InI W T₂ c w →
    InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1 (abelian₂ W A c (A.len c) • w) →
    (∃ p ∈ Pp W Y (c - ((A.len c : ℕ) : ZMod n)) (A.len c), ∃ x ∈ W.Nl Y c, W.map ι w = p - x) →
    ∀ (d : ℕ) (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL),
      IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol → PoleOK W A T₂ c b sol w

theorem arith_h (p h : ℕ) (hp : 2 ≤ p) : h < (p - 1) * (2 * h / (p - 1) + 1) := by
  have := Nat.lt_mul_div_succ (2 * h) (show 0 < p - 1 by omega)
  omega

theorem jumpsLe_of_win (A : ArcP n) (hA : A.OK) (T : LocLat G Qp LL O)
    (hT : Win W A T) : JumpsLe PD T A.h := by
  intro τ a ha
  obtain ⟨i, hi⟩ := W.emb_bij.2 (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))
  have hw := hT.2 i τ hi.symm a ha
  have hok := hA.2.2.2.2.1 i
  have hGh := hA.2.2.2.2.2.1
  have hth := hA.2.2.2.2.2.2.2.1 i
  revert hw hok hth
  cases A.ty i with
  | thin =>
    intro hw _ _
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_Icc] at hw
    rw [abs_le]; constructor <;> omega
  | up b =>
    intro hw hok hth
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hw
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.ok] at hok
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.thick, Formalism.MainNotions.LocalTheoryWindows.LT.size, forall_const] at hth
    rw [abs_le]; constructor <;> omega
  | down b =>
    intro hw hok hth
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hw
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.ok] at hok
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.thick, Formalism.MainNotions.LocalTheoryWindows.LT.size, forall_const] at hth
    rw [abs_le]; constructor <;> omega

theorem lA_pow_smul (T : LocLat G Qp LL O) (k : ℕ) (x : W.DD T) :
    lA W ^ k • x = (((PD.p : ℕ) : O) ^ k) • x := by
  simp only [lA]
  rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem γA_lA_pow (g : W.Gam) (k : ℕ) : W.γA g (lA W ^ k) = lA W ^ k := by
  simp [lA, map_pow, map_natCast]

theorem Pp_letter (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (y : W.DD T)
    (hy : y ∈ Pp W T c e) : (letE (c + (e : ZMod n)) : LetA O n) • y = y := by
  let S : AddSubgroup (W.DD T) :=
    { carrier := {y | (letE (c + (e : ZMod n)) : LetA O n) • y = y}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢; rw [smul_add, ha, hb]
      zero_mem' := by simp only [Set.mem_ofPred_eq, smul_zero]
      neg_mem' := fun {a} ha => by simp only [Set.mem_ofPred_eq] at ha ⊢; rw [smul_neg, ha] }
  have hgen : {z | ∃ a ∈ W.AΔ, ∃ x, Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧ z = a • ((W.φD T) ^ e) x} ⊆
      (S : Set (W.DD T)) := by
    rintro _ ⟨a, -, x, ⟨-, ⟨y', -, hyx⟩⟩, rfl⟩
    have hxc : (letE c : LetA O n) • x = x := by
      rw [← hyx, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, letE_mul_self]
    show (letE (c + (e : ZMod n)) : LetA O n) • (a • ((W.φD T) ^ e) x) = a • ((W.φD T) ^ e) x
    rw [smul_comm, PhiPowers.φD_pow_letter W T c x hxc e]
  exact (AddSubgroup.closure_le S).2 hgen hy

theorem Pp_Δ (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) {y : W.DD T}
    (hy : y ∈ Pp W T c e) : ∀ δ ∈ W.DelF, W.γD T δ y = y := by
  intro δ hδ
  let S : AddSubgroup (W.DD T) :=
    { carrier := {y | W.γD T δ y = y}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢; rw [map_add, ha, hb]
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]
      neg_mem' := fun {a} ha => by simp only [Set.mem_ofPred_eq] at ha ⊢; rw [map_neg, ha] }
  have hgen : {z | ∃ a ∈ W.AΔ, ∃ x, Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧ z = a • ((W.φD T) ^ e) x} ⊆
      (S : Set (W.DD T)) := by
    rintro _ ⟨a, ha, x, ⟨hxN, -⟩, rfl⟩
    show W.γD T δ (a • ((W.φD T) ^ e) x) = a • ((W.φD T) ^ e) x
    rw [Formalism.MainNotions.WachCoordinates.Br.γD_smulA, ha δ hδ, PhiPowers.φD_pow_Δ W T hxN.2 e δ hδ]
  exact (AddSubgroup.closure_le S).2 hgen hy

theorem InFN_add {T : LocLat G Qp LL O} {f : LetA O n} {a b : W.DD T} (ha : InFN W T f a)
    (hb : InFN W T f b) : InFN W T f (a + b) := by
  obtain ⟨y₁, hy₁, rfl⟩ := ha
  obtain ⟨y₂, hy₂, rfl⟩ := hb
  exact ⟨y₁ + y₂, add_mem hy₁ hy₂, (smul_add f y₁ y₂).symm⟩

theorem InFN_sub {T : LocLat G Qp LL O} {f : LetA O n} {a b : W.DD T} (ha : InFN W T f a)
    (hb : InFN W T f b) : InFN W T f (a - b) := by
  obtain ⟨y₁, hy₁, rfl⟩ := ha
  obtain ⟨y₂, hy₂, rfl⟩ := hb
  exact ⟨y₁ - y₂, sub_mem hy₁ hy₂, (smul_sub f y₁ y₂).symm⟩

theorem InFN_zero (T : LocLat G Qp LL O) (f : LetA O n) : InFN W T f (0 : W.DD T) :=
  ⟨0, zero_mem _, (smul_zero f).symm⟩

theorem InFN_smulO {T : LocLat G Qp LL O} {f : LetA O n} {a : W.DD T} (r : O) (ha : InFN W T f a) :
    InFN W T f (r • a) := by
  obtain ⟨y, hy, rfl⟩ := ha
  exact ⟨r • y, Submodule.smul_of_tower_mem _ r hy, smul_comm r f y⟩

theorem InFN_sum {T : LocLat G Qp LL O} {f : LetA O n} {ι : Type} (s : Finset ι) (a : ι → W.DD T)
    (h : ∀ i ∈ s, InFN W T f (a i)) : InFN W T f (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using InFN_zero W T f
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    exact InFN_add W (h b (Finset.mem_insert_self b s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem clK_sum (T : LocLat G Qp LL O) {ι : Type} (s : Finset ι) (u zz : ι → W.DD T)
    (x : ι → LatticeCohomology T.L)
    (h : ∀ i ∈ s, ∃ hm : (u i, zz i) ∈ W.wachCocyclesDelta T, W.clK T ⟨(u i, zz i), hm⟩ = x i) :
    ∃ hm : (∑ i ∈ s, u i, ∑ i ∈ s, zz i) ∈ W.wachCocyclesDelta T,
      W.clK T ⟨(∑ i ∈ s, u i, ∑ i ∈ s, zz i), hm⟩ = ∑ i ∈ s, x i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simp only [Finset.sum_empty]; exact (W.wachCocyclesDelta T).zero_mem, ?_⟩
    simp only [Finset.sum_empty]
    exact map_zero (W.clK T)
  | insert b s hb ih =>
    obtain ⟨hm1, h1⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨hmb, hb'⟩ := h b (Finset.mem_insert_self b s)
    simp only [Finset.sum_insert hb]
    refine ⟨(W.wachCocyclesDelta T).add_mem hmb hm1, ?_⟩
    show W.clK T (⟨(u b, zz b), hmb⟩ + ⟨(∑ i ∈ s, u i, ∑ i ∈ s, zz i), hm1⟩) = _
    rw [map_add, hb', h1]

theorem clK_smul (T : LocLat G Qp LL O) (r : O) (y z : W.DD T) (hm : (y, z) ∈ W.wachCocyclesDelta T)
    (hm' : (r • y, r • z) ∈ W.wachCocyclesDelta T) :
    W.clK T ⟨(r • y, r • z), hm'⟩ = r • W.clK T ⟨(y, z), hm⟩ := by
  show W.clK T (r • ⟨(y, z), hm⟩) = _
  rw [map_smul]

theorem clK_congr (T : LocLat G Qp LL O) {y y' z z' : W.DD T} (hy : y = y') (hz : z = z')
    (h : (y, z) ∈ W.wachCocyclesDelta T) (h' : (y', z') ∈ W.wachCocyclesDelta T) :
    W.clK T ⟨(y, z), h⟩ = W.clK T ⟨(y', z'), h'⟩ := by
  subst hy hz
  rfl

theorem splitCore_of [NeZero n] (hO : Function.Injective (algebraMap O LL)) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hF1 : FirstWachFiltration W) (hRel : RelayCore W) (hExt : Formalism.MainNotions.RamifiedCoefficientChains.HerrExt W)
    (hLift : SplitLift W) (hShape : SplitShape W) : SplitCore W := by
  intro hCA h5 A hA T₂ Y ι π hT₂ hY cc hc hext rr hK
  have hs : W.s = 1 := hCA.2.1
  have hp : PD.p ≠ 2 := hCA.2.2
  have hg : W.gamK = W.gam := W.gamK_eq_one hs hp
  have hπ : W.π₀ ∈ W.AΔ := ((h9 T₂ hT₂.1 hs hp).2.2 (finrank_one_of_bij hCA.1)).1.1
  obtain ⟨e, e₀, hU, -, hEK⟩ := hExt
  obtain ⟨heN, heSpan, -, heφ, heγ, he₀⟩ := hU
  obtain ⟨hses, et, het, hspan, hcc⟩ := hext

  have he₀mem : e₀ ∈ Submodule.span O {π.f et} := by
    rw [hspan, he₀]; exact Submodule.mem_span_singleton_self e₀
  have hetmem : π.f et ∈ Submodule.span O {e₀} := by
    rw [← he₀, ← hspan]; exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 he₀mem
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hetmem
  have hab : a * b = 1 := by
    have h1 : (a * b - 1) • e₀ = 0 := by
      rw [sub_smul, mul_smul, hb, ha, one_smul, sub_self]
    have h2 : algebraMap O LL (a * b - 1) • e₀ = 0 := by rw [algebraMap_smul]; exact h1
    rcases smul_eq_zero.1 h2 with h3 | h3
    · have : a * b - 1 = 0 := hO (by rw [h3, map_zero])
      exact sub_eq_zero.1 this
    · exfalso
      obtain ⟨e1, he1, he1s⟩ := W.one_line
      have hm : e1 ∈ W.one.L.T := by rw [he1s]; exact Submodule.mem_span_singleton_self e1
      rw [he₀, h3, Submodule.mem_span_singleton] at hm
      obtain ⟨r, hr⟩ := hm
      exact he1 (by rw [← hr, smul_zero])

  have hκ : a • cc ∈ latticeCocycles T₂.L := (latticeCocycles T₂.L).smul_mem a hc
  have hcoc : Formalism.MainNotions.RamifiedCoefficientChains.IsCocOf W ι π e₀ (a • cc) := by
    refine ⟨hses, a • et, Y.L.T.smul_mem a het, ?_, fun g => ?_⟩
    · rw [π.f.map_smul_of_tower, ha]
    · rw [Pi.smul_apply, ι.f.map_smul_of_tower, hcc g, (Y.ρ g).map_smul_of_tower, smul_sub]

  obtain ⟨xt, y, z, w, τ, hxΔ, hxπ, hyι, hzι, hyz, hzN, hcut, hsum⟩ :=
    hLift hCA h5 A hA T₂ Y ι π hT₂ hY hses rr hK e heN heSpan heφ heγ b
  have hzγK : W.map ι z = W.γD Y W.gamK xt - xt := by rw [hg]; exact hzι
  have hclass := hEK hs hp T₂ Y ι π (a • cc) hκ hcoc xt
    (b * ((PD.p : ℕ) : O) ^ (rr + A.σ PD.p)) hxπ hxΔ ⟨(y, z), hyz⟩ hyι hzγK

  have hJ := jumpsLe_of_win W A hA T₂ hT₂
  have hlt : A.h < (PD.p - 1) * A.M PD.p := arith_h PD.p A.h (by omega)
  obtain ⟨-, hF1uniq, hF1cls, -, -⟩ := (hF1 hCA A.h (A.M PD.p) hlt).1 T₂ hT₂.1 hJ

  have hcls : ∀ c ∈ A.cuts, ∃ xc, Cls W T₂ (A.M PD.p)
      (lA W ^ A.σ PD.p • ((W.φD T₂) ^ A.j) (w c) - τ c) xc := by
    intro c hc
    obtain ⟨hI, -, hTr, -⟩ := hcut c hc
    have hR := ((hRel hCA h5 A hA c hc).1 T₂ hT₂).2.1 (w c) hI
    have hγ := hR.2.2.1 (τ c) hTr
    obtain ⟨τ', hτ', hτeq⟩ := hTr.1
    refine hF1cls (c + (A.j : ZMod n)) _ ?_ ?_ hγ
    · show (letE (c + (A.j : ZMod n)) : LetA O n) •
          (lA W ^ A.σ PD.p • ((W.φD T₂) ^ A.j) (w c) - τ c) = _
      rw [hτeq, smul_sub, smul_comm _ (lA W ^ A.σ PD.p), PhiPowers.φD_pow_letter W T₂ c (w c) hI.1 A.j,
        smul_comm _ W.π₀, Pp_letter W T₂ c A.j τ' hτ']
    · intro δ hδ
      rw [hτeq, map_sub, Formalism.MainNotions.WachCoordinates.Br.γD_smulA, γA_lA_pow, PhiPowers.φD_pow_Δ W T₂ hI.2.1 A.j δ hδ,
        Formalism.MainNotions.WachCoordinates.Br.γD_smulA,
        hπ δ hδ, Pp_Δ W T₂ c A.j hτ' δ hδ]
  choose! xc hxc using hcls
  have hcls2 : ∀ c ∈ A.cuts, ∃ zc : W.DD T₂, InFN W T₂ (W.π₀ ^ A.M PD.p) zc ∧
      ∃ hm : (lA W ^ A.σ PD.p • ((W.φD T₂) ^ A.j) (w c) - τ c, zc) ∈ W.wachCocyclesDelta T₂,
        W.clK T₂ ⟨_, hm⟩ = xc c := by
    intro c hc
    obtain ⟨zc, hm, hzc, hcl⟩ := hxc c hc
    exact ⟨zc, hzc, hm, hcl⟩
  choose! zc hzc hzcm using hcls2
  obtain ⟨hmS, hS⟩ := clK_sum W T₂ A.cuts
    (fun c => lA W ^ A.σ PD.p • ((W.φD T₂) ^ A.j) (w c) - τ c) zc xc (fun c hc => hzcm c hc)

  set r : O := ((PD.p : ℕ) : O) ^ A.σ PD.p with hr
  have hm2 : (r • y, r • z) ∈ W.wachCocyclesDelta T₂ := (W.wachCocyclesDelta T₂).smul_mem r hyz
  have hsum' : ∑ c ∈ A.cuts, (lA W ^ A.σ PD.p • ((W.φD T₂) ^ A.j) (w c) - τ c) = r • y := by
    rw [hsum, lA_pow_smul]
  have hZ : ∑ c ∈ A.cuts, zc c = r • z := by
    have c1 := ((mem_Z1DΔ (W := W) (T := T₂) _ _).1 hmS).1
    have c2 := ((mem_Z1DΔ (W := W) (T := T₂) _ _).1 hm2).1
    rw [hsum'] at c1
    have hd0 : W.φD T₂ (∑ c ∈ A.cuts, zc c - r • z) - (∑ c ∈ A.cuts, zc c - r • z) = 0 := by
      rw [map_sub]
      have := c1.symm.trans c2
      rw [← sub_eq_zero] at this
      rw [← this]; abel
    have hdN : InFN W T₂ (W.π₀ ^ A.M PD.p) (∑ c ∈ A.cuts, zc c - r • z) :=
      InFN_sub W (InFN_sum W A.cuts zc fun c hc => hzc c hc) (InFN_smulO W r hzN)
    obtain ⟨x0, -, -, hx0⟩ := hF1uniq 0 (InFN_zero W T₂ _)
    have e1 := hx0 _ hdN hd0
    have e2 := hx0 0 (InFN_zero W T₂ _) (by simp)
    exact sub_eq_zero.1 (e1.trans e2.symm)

  refine ⟨w, xc, fun c hc => ?_, Or.inl ?_⟩
  · obtain ⟨hI, hP, hTr, hsh⟩ := hcut c hc
    exact ⟨hI, hP, ⟨τ c, hTr, hxc c hc⟩,
      fun d bb sol hH => hShape hCA h5 A hA T₂ Y ι π hT₂ hY hses c hc (w c) hI hP hsh d bb sol hH⟩
  · have hcl2 : W.clK T₂ ⟨(y, z), hyz⟩ =
        (b * ((PD.p : ℕ) : O) ^ (rr + A.σ PD.p)) • Formalism.MainNotions.RamifiedCoefficientChains.clsK T₂ (a • cc) hκ := hclass
    rw [← hS, clK_congr W T₂ hsum' hZ hmS hm2, clK_smul W T₂ r y z hyz hm2, hcl2]
    simp only [Formalism.MainNotions.RamifiedCoefficientChains.clsK]
    rw [show (⟨a • cc, hκ⟩ : ↥(latticeCocycles T₂.L)) = a • ⟨cc, hc⟩ from rfl, Submodule.Quotient.mk_smul,
      smul_smul, smul_smul, hr]
    congr 1
    linear_combination (-(((PD.p : ℕ) : O) ^ (rr + 2 * A.σ PD.p))) * hab

def SplitLiftL (D : D7) (HW : HWOf D.loc) : Prop :=
  AtCaseA fun l _ K LL hG => SplitLift ((HW l).W K 1 LL hG)

def SplitShapeL (D : D7) (HW : HWOf D.loc) : Prop :=
  AtCaseA fun l _ K LL hG => SplitShape ((HW l).W K 1 LL hG)

end Formalism.MainNotions.UnusedSlot80.Split

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem splitting_of_lift_and_shape (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hL : Split.SplitLiftL D HW) (hS : Split.SplitShapeL D HW) :
    SplittingTheoremArcLifting D HW F Cm := by
  rintro ⟨-, h9, -, -, hExt, hF1, hRel, -⟩ l _ K LL hG hA h5
  have := neZero_finrank_max_unramified K
  exact Split.splitCore_of _ (fun x y h => Subtype.ext h) (h9 l K 1 LL hG) (hF1 l K LL hG hA h5)
    (hRel l K LL hG hA h5) (hExt l K 1 LL hG) (hL l K LL hG hA h5) (hS l K LL hG hA h5)

end Formalism.MainNotions.UnusedSlot80

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.Split

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def DDExact : Prop :=
  ∀ (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L),
    IsCrys PD T₂.ρ → IsCrys PD Y.ρ → IsSESLat (Qp := Qp) ι π →
    (∀ x, W.map π (W.map ι x) = 0) ∧ (∀ x, W.map ι x = 0 → x = 0) ∧
      ∀ u, W.map π u = 0 → ∃ x, W.map ι x = u

def xsh (A : ArcP n) {T₂ Y : LocLat G Qp LL O} (ι : LatHom T₂.L Y.L) (x : ZMod n → W.DD Y)
    (τ₂ : ZMod n → W.DD T₂) (c : ZMod n) : W.DD Y :=
  lA W ^ A.σ PD.p • ((W.φD Y) ^ A.j) (x c) - W.map ι (τ₂ c)

def CutData : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ A : ArcP n, A.OK →
  ∀ (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L),
    Win W A T₂ → IsCrys PD Y.ρ → IsSESLat (Qp := Qp) ι π →
    ∀ rr : ℕ, (∀ c ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W π c (Formalism.MainNotions.LiftingTheory.lp W rr)) →
    ∀ e : W.DD W.one, e ∈ W.N W.one → W.N W.one = Submodule.span (LetA O n) {e} →
      W.φD W.one e = e → (∀ g, W.γD W.one g e = e) → ∀ b : O,
    ∃ (x : ZMod n → W.DD Y) (τ₂ m : ZMod n → W.DD T₂), ∀ c ∈ A.cuts,
      x c ∈ W.Nl Y c ∧
      W.map π (x c) = (b * ((PD.p : ℕ) : O) ^ rr) • ((letE c : LetA O n) • e) ∧
      xsh W A ι x τ₂ c ∈ Pp W Y c A.j ∧
      (∀ δ ∈ W.DelF, W.γD Y δ (xsh W A ι x τ₂ c) = xsh W A ι x τ₂ c) ∧
      m c ∈ W.NΔ T₂ ∧
      W.γ Y (xsh W A ι x τ₂ c) - xsh W A ι x τ₂ c = W.map ι (W.π₀ ^ A.M PD.p • m c) ∧
      ∀ w : W.DD T₂, W.map ι w = ((W.φD Y) ^ (A.len c - A.j))
          (xsh W A ι x τ₂ (c - ((A.len c : ℕ) : ZMod n))) - lA W ^ A.σ PD.p • x c →
        InI W T₂ c w ∧
        InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1 (abelian₂ W A c (A.len c) • w) ∧
        IsTr W A T₂ c w (-(lA W ^ A.σ PD.p • τ₂ c))

theorem arc_inj (A : ArcP n) (hA : A.OK) {c₁ c₂ : ZMod n} (h₁ : c₁ ∈ A.cuts) (h₂ : c₂ ∈ A.cuts)
    {k₁ k₂ : ℕ} (hk₁ : k₁ < A.len c₁) (hk₂ : k₂ < A.len c₂)
    (h : c₁ - ((A.len c₁ : ℕ) : ZMod n) + (k₁ : ZMod n) = c₂ - ((A.len c₂ : ℕ) : ZMod n) + (k₂ : ZMod n)) :
    c₁ = c₂ ∧ k₁ = k₂ := by
  have hcut := hA.2.2.1
  have key : ∀ {c₁ c₂ : ZMod n} {k₁ k₂ : ℕ}, c₁ ∈ A.cuts → c₂ ∈ A.cuts → k₁ < A.len c₁ → k₂ < A.len c₂ →
      k₁ ≤ k₂ → c₁ - ((A.len c₁ : ℕ) : ZMod n) + (k₁ : ZMod n) = c₂ - ((A.len c₂ : ℕ) : ZMod n) + (k₂ : ZMod n) →
      k₁ = k₂ := by
    intro c₁ c₂ k₁ k₂ h₁ h₂ hk₁ hk₂ hle h
    by_contra hne
    have hlt : k₁ < k₂ := lt_of_le_of_ne hle hne
    have ha : c₁ - ((A.len c₁ : ℕ) : ZMod n) = c₂ - ((A.len c₂ - k₂ + k₁ : ℕ) : ZMod n) := by
      rw [Nat.cast_add, Nat.cast_sub hk₂.le]
      linear_combination h
    exact (hcut c₂ h₂).2.2.2 (A.len c₂ - k₂ + k₁) (by omega) (by omega) (ha ▸ (hcut c₁ h₁).2.2.1)
  have hk : k₁ = k₂ := by
    rcases le_total k₁ k₂ with hle | hle
    · exact key h₁ h₂ hk₁ hk₂ hle h
    · exact (key h₂ h₁ hk₂ hk₁ hle h.symm).symm
  subst hk
  refine ⟨?_, rfl⟩
  have h' : c₁ - ((A.len c₁ : ℕ) : ZMod n) = c₂ - ((A.len c₂ : ℕ) : ZMod n) := add_right_cancel h
  rcases lt_trichotomy (A.len c₁) (A.len c₂) with hl | hl | hl
  · exfalso
    apply (hcut c₂ h₂).2.2.2 (A.len c₂ - A.len c₁) (by omega) (by have := (hcut c₁ h₁).1; omega)
    have e : c₂ - ((A.len c₂ - A.len c₁ : ℕ) : ZMod n) = c₁ := by
      rw [Nat.cast_sub hl.le]
      linear_combination -h'
    rw [e]
    exact h₁
  · rw [hl] at h'
    exact sub_left_injective h'
  · exfalso
    apply (hcut c₁ h₁).2.2.2 (A.len c₁ - A.len c₂) (by omega) (by have := (hcut c₂ h₂).1; omega)
    have e : c₁ - ((A.len c₁ - A.len c₂ : ℕ) : ZMod n) = c₂ := by
      rw [Nat.cast_sub hl.le]
      linear_combination h'
    rw [e]
    exact h₂

theorem arc_surj [NeZero n] (A : ArcP n) (hA : A.OK) (i : ZMod n) :
    ∃ c ∈ A.cuts, ∃ k < A.len c, c - ((A.len c : ℕ) : ZMod n) + (k : ZMod n) = i := by
  classical
  have hex : ∃ d : ℕ, 1 ≤ d ∧ i + (d : ZMod n) ∈ A.cuts := by
    obtain ⟨c0, hc0⟩ := hA.1
    refine ⟨(c0 - i).val + n, by have := NeZero.pos n; omega, ?_⟩
    rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero, add_sub_cancel]
    exact hc0
  have hd1 := (Nat.find_spec hex).1
  have hdc := (Nat.find_spec hex).2
  obtain ⟨hl1, -, hprev, -⟩ := hA.2.2.1 _ hdc
  have hdl : Nat.find hex ≤ A.len (i + (Nat.find hex : ZMod n)) := by
    by_contra hcon
    push_neg at hcon
    apply Nat.find_min hex (m := Nat.find hex - A.len (i + (Nat.find hex : ZMod n))) (by omega)
    refine ⟨by omega, ?_⟩
    have e : i + ((Nat.find hex - A.len (i + (Nat.find hex : ZMod n)) : ℕ) : ZMod n) =
        i + (Nat.find hex : ZMod n) - ((A.len (i + (Nat.find hex : ZMod n)) : ℕ) : ZMod n) := by
      rw [Nat.cast_sub hcon.le]
      ring
    rw [e]
    exact hprev
  refine ⟨i + (Nat.find hex : ZMod n), hdc, A.len (i + (Nat.find hex : ZMod n)) - Nat.find hex, by omega, ?_⟩
  rw [Nat.cast_sub hdl]
  ring

theorem sum_arcs [NeZero n] (A : ArcP n) (hA : A.OK) {M : Type} [AddCommMonoid M] (f : ZMod n → M) :
    ∑ c ∈ A.cuts, ∑ k ∈ Finset.range (A.len c), f (c - ((A.len c : ℕ) : ZMod n) + (k : ZMod n)) =
      ∑ i, f i := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun x _ => x.1 - ((A.len x.1 : ℕ) : ZMod n) + (x.2 : ZMod n))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨c₁, k₁⟩ h₁ ⟨c₂, k₂⟩ h₂ h
    rw [Finset.mem_sigma, Finset.mem_range] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := arc_inj A hA h₁.1 h₂.1 h₁.2 h₂.2 h
    rfl
  · intro i _
    obtain ⟨c, hc, k, hk, h⟩ := arc_surj A hA i
    exact ⟨⟨c, k⟩, Finset.mem_sigma.2 ⟨hc, Finset.mem_range.2 hk⟩, h⟩

theorem sum_prev [NeZero n] (A : ArcP n) (hA : A.OK) {M : Type} [AddCommMonoid M] (g : ZMod n → M) :
    ∑ c ∈ A.cuts, g (c - ((A.len c : ℕ) : ZMod n)) = ∑ c ∈ A.cuts, g c := by
  refine Finset.sum_bij (fun c _ => c - ((A.len c : ℕ) : ZMod n)) (fun c hc => (hA.2.2.1 c hc).2.2.1) ?_ ?_
    (fun _ _ => rfl)
  · intro c₁ h₁ c₂ h₂ h
    exact (arc_inj A hA h₁ h₂ (k₁ := 0) (k₂ := 0) (by have := (hA.2.2.1 c₁ h₁).1; omega)
      (by have := (hA.2.2.1 c₂ h₂).1; omega) (by simpa using h)).1
  · intro c' hc'
    obtain ⟨c, hc, k, hk, h⟩ := arc_surj A hA c'
    have hk0 : k = 0 := by
      by_contra hne
      apply (hA.2.2.1 c hc).2.2.2 (A.len c - k) (by omega) (by omega)
      have e : c - ((A.len c - k : ℕ) : ZMod n) = c' := by
        rw [Nat.cast_sub hk.le, ← h]
        ring
      rw [e]
      exact hc'
    subst hk0
    exact ⟨c, hc, by simpa using h⟩

theorem map_φpow {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (k : ℕ) (x : W.DD T) :
    W.map f (((W.φD T) ^ k) x) = ((W.φD T') ^ k) (W.map f x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [PhiPowers.pow_apply_succ, PhiPowers.pow_apply_succ, ← ih]
    first
    | exact W.map_φ f _
    | exact (W.map_φ f _).symm
    | simp [W.map_φ]

theorem φpow_smulA (T : LocLat G Qp LL O) (k : ℕ) (a : LetA O n) (x : W.DD T) :
    ((W.φD T) ^ k) (a • x) = (W.φA ^ k) a • ((W.φD T) ^ k) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [PhiPowers.pow_apply_succ, ih, φD_smulA, PhiPowers.pow_apply_succ, pow_succ']
    rfl

theorem φA_pow_lA (k s : ℕ) : (W.φA ^ k) (lA W ^ s) = lA W ^ s := by
  simp [lA, map_pow, map_natCast]

theorem φpow_smulO (T : LocLat G Qp LL O) (k : ℕ) (r : O) (x : W.DD T) :
    ((W.φD T) ^ k) (r • x) = r • ((W.φD T) ^ k) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [PhiPowers.pow_apply_succ, ih, PhiPowers.pow_apply_succ]
    first
    | exact map_smul (W.φD T) r _
    | exact W.φD_smulO T r _
    | (rw [← algebraMap_smul (LetA O n) r, φD_smulA, ← algebraMap_smul (LetA O n) r]
       congr 1
       first
       | exact AlgHom.commutes _ r
       | exact W.φA_alg r
       | simp)

theorem φ_letE_e (e : W.DD W.one) (he : W.φD W.one e = e) (i : ZMod n) (k : ℕ) :
    ((W.φD W.one) ^ k) ((letE i : LetA O n) • e) = (letE (i + (k : ZMod n)) : LetA O n) • e := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [PhiPowers.pow_apply_succ, ih, φD_smulA, he]
    have e1 : i + ((k + 1 : ℕ) : ZMod n) - 1 = i + (k : ZMod n) := by push_cast; ring
    rw [← φA_letE W (i + ((k + 1 : ℕ) : ZMod n)), e1]

theorem γ_φpow (T : LocLat G Qp LL O) (k : ℕ) (x : W.DD T) :
    W.γ T (((W.φD T) ^ k) x) = ((W.φD T) ^ k) (W.γ T x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [PhiPowers.pow_apply_succ, PhiPowers.pow_apply_succ, ← ih]
    first
    | exact (W.φγ_comm _ _ _).symm
    | exact W.φγ_comm _ _ _
    | (simp only [LocWach.γ]; exact (W.φγ_comm _ _ _).symm)
    | (simp only [LocWach.γ]; exact W.φγ_comm _ _ _)

theorem φpow_add (T : LocLat G Qp LL O) (a b : ℕ) (x : W.DD T) :
    ((W.φD T) ^ a) (((W.φD T) ^ b) x) = ((W.φD T) ^ (b + a)) x := by
  rw [add_comm, pow_add]
  rfl

theorem Pp_φpow (T : LocLat G Qp LL O) (c : ZMod n) (e m : ℕ) {y : W.DD T}
    (hy : y ∈ Pp W T c e) : ((W.φD T) ^ m) y ∈ Pp W T c (e + m) := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    apply AddSubgroup.subset_closure
    exact ⟨(W.φA ^ m) a, PhiPowers.φA_pow_mem_AΔ (W := W) ha m, x, hx, by rw [φpow_smulA, φpow_add]⟩
  | zero =>
    rw [map_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    rw [map_add]
    exact add_mem ha hb
  | neg a _ ha =>
    rw [map_neg]
    exact neg_mem ha

theorem InFN_φpow (T : LocLat G Qp LL O) (M : ℕ) (hq : qA W ∈ W.AΔ)
    (h1 : ∀ x ∈ W.NΔ T, InFN W T (W.π₀ ^ M * qA W) (W.φD T (W.π₀ ^ M • x)))
    {m : W.DD T} (hm : m ∈ W.NΔ T) (k : ℕ) :
    InFN W T (W.π₀ ^ M) (((W.φD T) ^ k) (W.π₀ ^ M • m)) := by
  induction k with
  | zero => exact ⟨m, hm, rfl⟩
  | succ k ih =>
    obtain ⟨y, hy, hyeq⟩ := ih
    rw [PhiPowers.pow_apply_succ, hyeq]
    obtain ⟨y', hy', hy'eq⟩ := h1 y hy
    rw [hy'eq, mul_smul]
    exact ⟨qA W • y', PhiPowers.smul_mem_NΔ (W := W) T hq hy', rfl⟩

theorem tele (T : LocLat G Qp LL O) (L : ℕ) (v : W.DD T) :
    W.φD T (∑ k ∈ Finset.range L, ((W.φD T) ^ k) v) - ∑ k ∈ Finset.range L, ((W.φD T) ^ k) v =
      ((W.φD T) ^ L) v - v := by
  rw [map_sum]
  rw [Finset.sum_congr rfl fun k _ => (PhiPowers.pow_apply_succ W T k v).symm]
  rw [← Finset.sum_sub_distrib, Finset.sum_range_sub (fun k => ((W.φD T) ^ k) v), pow_zero]
  rfl

theorem splitLift_of [NeZero n] (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hF1 : FirstWachFiltration W) (hEx : DDExact W)
    (hCut : CutData W) : SplitLift W := by
  intro hCA h5 A hA T₂ Y ι π hT₂ hY hses rr hK e heN heSpan heφ heγ b
  have hs : W.s = 1 := hCA.2.1
  have hp : PD.p ≠ 2 := hCA.2.2
  have hg : W.gamK = W.gam := W.gamK_eq_one hs hp
  have hπ : W.π₀ ∈ W.AΔ := ((h9 T₂ hT₂.1 hs hp).2.2 (finrank_one_of_bij hCA.1)).1.1
  have hq : qA W ∈ W.AΔ := W.AΔ.add_mem hπ (W.AΔ.natCast_mem _)
  obtain ⟨hπι, hinj, hmid⟩ := hEx T₂ Y ι π hT₂.1 hY hses
  obtain ⟨x, τ₂, m, hcut⟩ := hCut hCA h5 A hA T₂ Y ι π hT₂ hY hses rr hK e heN heSpan heφ heγ b
  have hJ := jumpsLe_of_win W A hA T₂ hT₂
  have hlt : A.h < (PD.p - 1) * A.M PD.p := arith_h PD.p A.h (by omega)
  have h1 := ((hF1 hCA A.h (A.M PD.p) hlt).1 T₂ hT₂.1 hJ).1
  set σ := A.σ PD.p with hσ
  set X := xsh W A ι x τ₂ with hX
  set cb : O := b * ((PD.p : ℕ) : O) ^ (rr + σ) with hcb
  have hpv : ∀ c ∈ A.cuts, c - ((A.len c : ℕ) : ZMod n) ∈ A.cuts := fun c hc => (hA.2.2.1 c hc).2.2.1
  have hXπ : ∀ c ∈ A.cuts,
      W.map π (X c) = cb • ((letE (c + (A.j : ZMod n)) : LetA O n) • e) := by
    intro c hc
    have hxπ := (hcut c hc).2.1
    simp only [hX, xsh]
    rw [map_sub, hπι, sub_zero, Formalism.MainNotions.WachCoordinates.Br.map_smulA, map_φpow, hxπ, φpow_smulO,
      φ_letE_e W e heφ, lA_pow_smul, smul_smul, hcb]
    congr 1; ring
  have hw : ∀ c, ∃ wc : W.DD T₂, c ∈ A.cuts → W.map ι wc =
      ((W.φD Y) ^ (A.len c - A.j)) (X (c - ((A.len c : ℕ) : ZMod n))) - lA W ^ σ • x c := by
    intro c
    by_cases hc : c ∈ A.cuts
    · have hjL : A.j ≤ A.len c := hA.2.2.2.1 c hc
      obtain ⟨wc, hwc⟩ := hmid (((W.φD Y) ^ (A.len c - A.j)) (X (c - ((A.len c : ℕ) : ZMod n))) -
          lA W ^ σ • x c) (by
        rw [map_sub, map_φpow, hXπ _ (hpv c hc), φpow_smulO, φ_letE_e W e heφ,
          Formalism.MainNotions.WachCoordinates.Br.map_smulA, (hcut c hc).2.1, lA_pow_smul, smul_smul,
          show c - ((A.len c : ℕ) : ZMod n) + (A.j : ZMod n) + ((A.len c - A.j : ℕ) : ZMod n) = c by
            rw [Nat.cast_sub hjL]; ring, hcb, sub_eq_zero]
        congr 1; ring)
      exact ⟨wc, fun _ => hwc⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose w hwι using hw
  set xt : W.DD Y := ∑ c ∈ A.cuts, ∑ k ∈ Finset.range (A.len c),
    ((W.φD Y) ^ k) (X (c - ((A.len c : ℕ) : ZMod n))) with hxt
  have hterm : ∀ c ∈ A.cuts, ∀ k : ℕ, W.map π (((W.φD Y) ^ k) (X (c - ((A.len c : ℕ) : ZMod n)))) =
      cb • ((letE (c - ((A.len c : ℕ) : ZMod n) + (k : ZMod n) + (A.j : ZMod n)) : LetA O n) • e) := by
    intro c hc k
    rw [map_φpow, hXπ _ (hpv c hc), φpow_smulO, φ_letE_e W e heφ]
    congr 3; ring
  have hxtπ : W.map π xt = cb • e := by
    calc W.map π xt = ∑ c ∈ A.cuts, ∑ k ∈ Finset.range (A.len c),
          cb • ((letE (c - ((A.len c : ℕ) : ZMod n) + (k : ZMod n) + (A.j : ZMod n)) : LetA O n) • e) := by
          rw [hxt, map_sum]
          exact Finset.sum_congr rfl fun c hc =>
            (map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => hterm c hc k)
      _ = ∑ i, cb • ((letE (i + (A.j : ZMod n)) : LetA O n) • e) :=
          sum_arcs A hA (fun i => cb • ((letE (i + (A.j : ZMod n)) : LetA O n) • e))
      _ = cb • e := by
          rw [← Finset.smul_sum, ← Finset.sum_smul,
            Fintype.sum_equiv (Equiv.addRight (A.j : ZMod n)) (fun i => (letE (i + (A.j : ZMod n)) : LetA O n))
              (fun i => (letE i : LetA O n)) (fun _ => rfl), sum_letE, one_smul]
  have hφπ : W.map π (W.φD Y xt - xt) = 0 := by
    rw [map_sub, W.map_φ, hxtπ, map_smul, heφ, sub_self]
  obtain ⟨y, hy⟩ := hmid _ hφπ
  have hγπ : W.map π (W.γD Y W.gam xt - xt) = 0 := by
    rw [map_sub, W.map_γ, hxtπ, map_smul, heγ, sub_self]
  obtain ⟨z, hz⟩ := hmid _ hγπ
  have hz' : W.map ι z = W.γD Y W.gam xt - xt := hz
  have hxtΔ : ∀ δ ∈ W.DelF, W.γD Y δ xt = xt := by
    intro δ hδ
    rw [hxt, map_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact PhiPowers.φD_pow_Δ W Y (hcut _ (hpv c hc)).2.2.2.1 k δ hδ
  set Z : W.DD T₂ := ∑ c ∈ A.cuts, ∑ k ∈ Finset.range (A.len c),
    ((W.φD T₂) ^ k) (W.π₀ ^ A.M PD.p • m (c - ((A.len c : ℕ) : ZMod n))) with hZ
  have hιZ : W.map ι Z = W.γD Y W.gam xt - xt := by
    rw [hZ, hxt, map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_φpow, ← (hcut _ (hpv c hc)).2.2.2.2.2.1, map_sub]
    have := γ_φpow W Y k (X (c - ((A.len c : ℕ) : ZMod n)))
    simp only [LocWach.γ] at this
    rw [this]
    rfl
  have hzZ : z = Z := by
    have h0 : W.map ι (z - Z) = 0 := by rw [map_sub, hz', hιZ, sub_self]
    exact sub_eq_zero.1 (hinj _ h0)
  have hzN : InFN W T₂ (W.π₀ ^ A.M PD.p) z := by
    rw [hzZ, hZ]
    exact InFN_sum W _ _ fun c hc => InFN_sum W _ _ fun k _ =>
      InFN_φpow W T₂ _ hq h1 (hcut _ (hpv c hc)).2.2.2.2.1 k
  have hyz : (y, z) ∈ W.wachCocyclesDelta T₂ := by
    rw [mem_Z1DΔ (W := W) (T := T₂)]
    refine ⟨?_, fun δ hδ => ?_, fun δ hδ => ?_⟩
    · rw [hg]
      have h0 : W.map ι (W.γD T₂ W.gam y - y - (W.φD T₂ z - z)) = 0 := by
        simp only [map_sub, W.map_γ, W.map_φ, hy, hz', W.φγ_comm]
        abel
      exact sub_eq_zero.1 (hinj _ h0)
    · have h0 : W.map ι (W.γD T₂ δ y - y) = 0 := by
        simp only [map_sub, W.map_γ, hy, ← W.φγ_comm, hxtΔ δ hδ, sub_self]
      exact sub_eq_zero.1 (hinj _ h0)
    · have hcomm : W.γD Y δ (W.γD Y W.gam xt) = W.γD Y W.gam xt := by
        rw [← W.γD_mul, mul_comm, W.γD_mul, hxtΔ δ hδ]
      have h0 : W.map ι (W.γD T₂ δ z - z) = 0 := by
        simp only [map_sub, W.map_γ, hz', hcomm, hxtΔ δ hδ, sub_self]
      exact sub_eq_zero.1 (hinj _ h0)
  have hφxt : W.φD Y xt - xt = ∑ c ∈ A.cuts, (((W.φD Y) ^ A.len c) (X (c - ((A.len c : ℕ) : ZMod n))) -
      X (c - ((A.len c : ℕ) : ZMod n))) := by
    rw [hxt, map_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => tele W Y _ _
  have hR : ∑ c ∈ A.cuts, (((W.φD Y) ^ A.len c) (X (c - ((A.len c : ℕ) : ZMod n))) -
      X (c - ((A.len c : ℕ) : ZMod n))) =
      ∑ c ∈ A.cuts, (((W.φD Y) ^ A.len c) (X (c - ((A.len c : ℕ) : ZMod n))) - X c) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_prev A hA X]
  refine ⟨xt, y, z, w, fun c => -(lA W ^ σ • τ₂ c), hxtΔ, hxtπ, hy, hz, hyz, hzN, fun c hc => ?_, ?_⟩
  · obtain ⟨hxN, -, -, -, -, -, hW⟩ := hcut c hc
    obtain ⟨hI, hP, hTr⟩ := hW (w c) (hwι c hc)
    refine ⟨hI, hP, hTr, ((W.φD Y) ^ (A.len c - A.j)) (X (c - ((A.len c : ℕ) : ZMod n))), ?_,
      lA W ^ σ • x c, (W.Nl Y c).smul_mem _ hxN, hwι c hc⟩
    have := Pp_φpow W Y _ A.j (A.len c - A.j) (hcut _ (hpv c hc)).2.2.1
    rwa [Nat.add_sub_cancel' (hA.2.2.2.1 c hc)] at this
  · beta_reduce
    have key : W.map ι (∑ c ∈ A.cuts, (lA W ^ σ • ((W.φD T₂) ^ A.j) (w c) - -(lA W ^ σ • τ₂ c))) =
        W.map ι (lA W ^ σ • y) := by
      rw [Formalism.MainNotions.WachCoordinates.Br.map_smulA, hy, hφxt, hR, Finset.smul_sum, map_sum]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [map_sub, map_neg, Formalism.MainNotions.WachCoordinates.Br.map_smulA, Formalism.MainNotions.WachCoordinates.Br.map_smulA, map_φpow, hwι c hc,
        map_sub, φpow_smulA, φA_pow_lA, φpow_add, Nat.sub_add_cancel (hA.2.2.2.1 c hc)]
      simp only [hX, xsh]
      rw [smul_sub, smul_sub, smul_sub]
      abel
    exact sub_eq_zero.1 (hinj _ (by rw [map_sub, key, sub_self]))

def DDExactL (D : D7) (HW : HWOf D.loc) : Prop :=
  AtCaseA fun l _ K LL hG => DDExact ((HW l).W K 1 LL hG)

def CutDataL (D : D7) (HW : HWOf D.loc) : Prop :=
  AtCaseA fun l _ K LL hG => CutData ((HW l).W K 1 LL hG)

end Formalism.MainNotions.UnusedSlot80.Split

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem splitting_of_exactness_and_data (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hX : Split.DDExactL D HW) (hC : Split.CutDataL D HW)
    (hS : Split.SplitShapeL D HW) : SplittingTheoremArcLifting D HW F Cm := by
  intro hAdm
  refine splitting_of_lift_and_shape D HW F Cm (fun l _ K LL hG hA h5 => ?_) hS hAdm
  have := neZero_finrank_max_unramified K
  exact Split.splitLift_of _ (hAdm.2.1 l K 1 LL hG) (hAdm.2.2.2.2.2.1 l K LL hG hA h5)
    (hX l K LL hG hA h5) (hC l K LL hG hA h5)

end Formalism.MainNotions.UnusedSlot80
