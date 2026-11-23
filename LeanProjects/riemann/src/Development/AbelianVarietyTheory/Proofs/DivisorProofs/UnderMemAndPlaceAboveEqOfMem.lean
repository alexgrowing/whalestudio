import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.FunObj.GivenAdm

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

section Local

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def CongM {a b : Type*} (c : kˣ) (X : Matrix a b k) : Prop := ∀ i j, valuation k (X i j) ≤ valuation k (c : k)

theorem mem_matLat_smul {a b : Type*} {c : kˣ} {X : Matrix a b k} : X ∈ matLat a (c • SplitFlip.stdLat k b) ↔ CongM c X := by
  rw [SplitFlip.stdLat, smul_diagLat, mem_matLat]
  simp [mem_diagLat, CongM]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem CongM.add {a b : Type*} {c : kˣ} {X Y : Matrix a b k} (h : CongM c X) (h' : CongM c Y) : CongM c (X + Y) :=
  fun i j => Valuation.map_add_le _ (h i j) (h' i j)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem CongM.mul_left {a b l : Type*} [Fintype a] {c : kˣ} {X : Matrix a b k} {Y : Matrix l a k} (h : CongM c X)
    (h' : IntM Y) : CongM c (Y * X) := fun i j => by
  refine Valuation.map_sum_le _ fun s _ => ?_
  rw [map_mul]
  exact (mul_le_of_le_one_left' (h' i s)).trans (h s j)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem CongM.mul_right {a b l : Type*} [Fintype b] {c : kˣ} {X : Matrix a b k} {Y : Matrix b l k} (h : CongM c X)
    (h' : IntM Y) : CongM c (X * Y) := fun i j => by
  refine Valuation.map_sum_le _ fun s _ => ?_
  rw [map_mul]
  exact (mul_le_of_le_one_right' (h' s j)).trans (h i s)

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem mem_glLatCong {c : kˣ} {g : GL a k} : g ∈ glLatCong c (SplitFlip.stdLat k a) ↔ g ∈ KO k a ∧ CongM c (g.val - 1) := by
  change g ∈ glLat _ ∧ (∀ x ∈ SplitFlip.stdLat k a, x ᵥ* (g.val - 1) ∈ c • SplitFlip.stdLat k a) ↔ _
  rw [glLat_stdLat]
  refine and_congr_right fun _ => ⟨fun h => mem_matLat_smul.1 fun i => ?_, fun h x hx => ?_⟩
  · have := h (Pi.single i 1) (mem_stdLat.2 fun l => by
      by_cases h : l = i
      · subst h; simp
      · simp [h])
    rwa [single_one_vecMul] at this
  · have h1 : IntM (Matrix.of fun (_ : Unit) => x) := fun _ j => mem_stdLat.1 hx j
    exact mem_matLat_smul.2 (h.mul_left h1) ()

theorem isOpen_glLatCong (c : kˣ) : IsOpen (glLatCong c (SplitFlip.stdLat k a) : Set (GL a k)) := by
  have e : (glLatCong c (SplitFlip.stdLat k a) : Set (GL a k)) =
      (KO k a : Set (GL a k)) ∩ ⋂ i, ⋂ j, (fun g : GL a k => (g.val - 1) i j / (c : k)) ⁻¹' (𝒪[k] : Set k) := by
    have h0 : 0 < valuation k (c : k) := zero_lt_iff.2 (by simp)
    ext g
    simp only [SetLike.mem_coe, mem_glLatCong, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, CongM,
      Valuation.mem_integer_iff, map_div₀, div_le_one₀ h0]
  rw [e]
  refine SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    IsOpen.preimage ?_ Valuation.isOpen_integer)
  have := Units.continuous_val (M := Matrix a a k)
  fun_prop

theorem invT_mem_glLatCong {c : kˣ} {g : GL a k} (h : g ∈ glLatCong c (SplitFlip.stdLat k a)) :
    invT g ∈ glLatCong c (SplitFlip.stdLat k a) := by
  have h' := mem_glLatCong.1 (inv_mem h)
  refine mem_glLatCong.2 ⟨invT_mem_KO (mem_glLatCong.1 h).1, fun i j => ?_⟩
  have := h'.2 j i
  rwa [invT_val, ← transpose_one, ← transpose_sub]

theorem gdet_mem_unitCong {c : kˣ} {g : GL a k} (h : g ∈ glLatCong c (SplitFlip.stdLat k a)) : gdet g ∈ unitCong c := by
  obtain ⟨h1, h2⟩ := mem_glLatCong.1 h
  refine ⟨valuation_gdet_of_mem_KO h1, ?_⟩
  obtain ⟨u, rfl⟩ := h1
  let I : Ideal 𝒪[k] := (Valuation.leSubmodule (valuation k) (valuation k (c : k))).comap (Algebra.linearMap 𝒪[k] k)
  have hI : ∀ x : 𝒪[k], x ∈ I ↔ valuation k (x : k) ≤ valuation k (c : k) := fun x =>
    Submodule.mem_comap.trans Valuation.mem_leSubmodule_iff
  have h3 : (Ideal.Quotient.mk I).mapMatrix u.val = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    refine Ideal.Quotient.eq.2 ((hI _).2 ?_)
    convert h2 i j using 2
    simp only [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> simp <;> rfl
  have h4 : u.val.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, h3, map_one, map_one, det_one]
  convert (hI _).1 h4 using 2
  push_cast
  congr 1
  exact ((algebraMap 𝒪[k] k).map_det u.val).symm

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in

theorem isNatDatum_cosets {ι : Type*} {p : ι → Prop} {f : ι → Matrix a b k} (hf : ∀ y, IntM (f y)) {ϖ : kˣ}
    (hϖ : IsUnif ϖ) {e' e : ℕ} (he : e' ≤ e) :
    IsNatDatum ϖ e (Set.indicator {x | ∃ y, p y ∧ x - f y ∈ matLat a (ϖ ^ e' • SplitFlip.stdLat k b)} 1) := by
  refine ⟨fun X hX => Set.indicator_of_notMem ?_ _, fun X Z hZ => ?_⟩
  · rintro ⟨y, -, hy⟩
    have h1 : X - f y ∈ matLat a (SplitFlip.stdLat k b) := fun i => pow_smul_le hϖ e' _ (hy i)
    exact hX (by simpa using add_mem h1 (mem_matLat_stdLat.2 (hf y)))
  · have hZ' : Z ∈ matLat a (ϖ ^ e' • SplitFlip.stdLat k b) := fun i => by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
      have := hZ i
      rw [pow_add, mul_comm, mul_smul] at this
      exact pow_smul_le hϖ d _ this
    refine Set.indicator_eq_indicator ?_ rfl
    refine exists_congr fun y => and_congr_right fun _ => ?_
    rw [add_sub_right_comm, add_mem_cancel_right hZ']

theorem indicator_cosets_mul {ι : Type*} {p : ι → Prop} {f : ι → Matrix a b k} (hf : ∀ y, IntM (f y)) {c : kˣ}
    {g : GL a k} {h : GL b k} (hg : g ∈ glLatCong c (SplitFlip.stdLat k a)) (hh : h ∈ glLatCong c (SplitFlip.stdLat k b)) (x : Matrix a b k) :
    Set.indicator {x | ∃ y, p y ∧ x - f y ∈ matLat a (c • SplitFlip.stdLat k b)} (1 : Matrix a b k → ℂ) (g.val * x * h.val) =
      Set.indicator {x | ∃ y, p y ∧ x - f y ∈ matLat a (c • SplitFlip.stdLat k b)} 1 x := by
  have key : ∀ {g : GL a k} {h : GL b k}, g ∈ glLatCong c (SplitFlip.stdLat k a) → h ∈ glLatCong c (SplitFlip.stdLat k b) → ∀ x y,
      CongM c (x - f y) → CongM c (g.val * x * h.val - f y) := fun {g h} hg hh x y hx => by
    obtain ⟨g1, g2⟩ := mem_glLatCong.1 hg
    obtain ⟨h1, h2⟩ := mem_glLatCong.1 hh
    have := (((hx.mul_left (intM_of_mem_KO g1)).mul_right (intM_of_mem_KO h1)).add
      ((g2.mul_right (hf y)).mul_right (intM_of_mem_KO h1))).add (h2.mul_left (hf y))
    convert this using 1
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one]
    abel
  refine Set.indicator_eq_indicator ?_ rfl
  refine exists_congr fun y => and_congr_right fun _ => ?_
  rw [mem_matLat_smul, mem_matLat_smul]
  refine ⟨fun H => ?_, key hg hh x y⟩
  have := key (inv_mem hg) (inv_mem hh) _ y H
  rwa [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
    Units.inv_mul, Matrix.one_mul] at this

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in

theorem isNatDatum_of_periodic {Φ : Matrix a b k → ℂ} (hs : ∀ x, Φ x ≠ 0 → IntM x)
    (hp : ∀ x y, MaxM y → Φ (x + y) = Φ x) {ϖ : kˣ} (hϖ : IsUnif ϖ) {e : ℕ} (he : 1 ≤ e) : IsNatDatum ϖ e Φ := by
  refine ⟨fun X hX => by_contra fun h => hX (mem_matLat_stdLat.2 (hs X h)), fun X Z hZ => hp X Z fun i j => ?_⟩
  refine (mem_matLat_smul.1 hZ i j).trans_lt ?_
  rw [Units.val_pow_eq_pow_val, map_pow, hϖ]
  exact pow_lt_one₀ zero_le uniformizer_lt_one (by omega)

theorem law_of_hasTypes {ν : kˣ →* ℂˣ} {P' : TypeDatum k a} {P : TypeDatum k b} {Φ : Matrix b a k → ℂ}
    (H : HasTypes ν P'.toLevel P.toLevel Φ) (g : P'.J) (h : P.J) (x : Matrix b a k) :
    (ν (gdet (g : GL a k)) : ℂ) * ((ν (gdet (h : GL b k)))⁻¹ : ℂˣ) * Φ (((h : GL b k)⁻¹).val * x * (g : GL a k).val) =
      ((P'.lam g / P.lam h : ℂˣ) : ℂ) * Φ x := by
  have h1 := congrFun (H.1 g) (((h : GL b k)⁻¹).val * x)
  have h2 := congrFun (H.2 h) x
  rw [om_of_mem_KO ν (P'.le_KO g.2) (one_mem _)] at h1
  rw [om_of_mem_KO ν (one_mem _) (P.le_KO h.2)] at h2
  simp only [map_one, inv_one, Units.val_one, mul_one, one_mul, Matrix.one_mul, Matrix.mul_one, Pi.smul_apply,
    smul_eq_mul] at h1 h2
  rw [div_eq_mul_inv, Units.val_mul, mul_assoc (P'.lam g : ℂ), ← h2]
  linear_combination (((ν (gdet (h : GL b k)))⁻¹ : ℂˣ) : ℂ) * h1

theorem hasTypes_vacuum : HasTypes 1 (TypeDatum.full k a).toLevel (TypeDatum.full k b).toLevel
    (Set.indicator {x : Matrix b a k | IntM x} 1) := by
  have key : ∀ {g : GL a k} {h : GL b k}, g ∈ KO k a → h ∈ KO k b →
      om 1 g h (Set.indicator {x : Matrix b a k | IntM x} 1) = Set.indicator {x : Matrix b a k | IntM x} 1 :=
    fun {g h} hg hh => funext fun x => by
      rw [om_of_mem_KO 1 hg hh]
      simp only [MonoidHom.one_apply, inv_one, Units.val_one, one_mul]
      refine Set.indicator_eq_indicator ?_ rfl
      exact mem_matLat_stdLat.symm.trans ((mul_mul_mem_matLat_iff (inv_mem hh) hg x).trans mem_matLat_stdLat)
  exact ⟨fun g => (key g.2 (one_mem _)).trans (one_smul _ _).symm,
    fun h => (key (one_mem _) h.2).trans (by
      rw [show (TypeDatum.full k b).lam h = 1 from rfl, inv_one, Units.val_one, one_smul])⟩

omit [Fintype b] [DecidableEq b] in
open Classical in

theorem parPhi_periodic {b' : Type*} {δ : kˣ →* ℂˣ} (hδ : IsTame δ) :
    (∀ x : Matrix (a ⊕ b) (a ⊕ b') k, parPhi δ x ≠ 0 → IntM x) ∧
      ∀ x y : Matrix (a ⊕ b) (a ⊕ b') k, MaxM y → parPhi δ (x + y) = parPhi δ x := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).1 hx
    rw [← fromBlocks_toBlocks x, ← e]
    exact intM_fromBlocks.2 ⟨intM_of_mem_KO hg, h12, h21.intM, h22⟩
  · rw [← fromBlocks_toBlocks y] at hy
    obtain ⟨y11, y12, y21, y22⟩ := maxM_fromBlocks.1 hy
    have e1 : MaxM (x + y).toBlocks₂₁ ↔ MaxM x.toBlocks₂₁ :=
      ⟨fun h => by simpa using (show MaxM (x.toBlocks₂₁ + y.toBlocks₂₁) from h).add y21.neg, fun h => h.add y21⟩
    have e2 : IntM (x + y).toBlocks₁₂ ↔ IntM x.toBlocks₁₂ :=
      ⟨fun h => by simpa using (show IntM (x.toBlocks₁₂ + y.toBlocks₁₂) from h).add y12.intM.neg,
        fun h => h.add y12.intM⟩
    have e3 : IntM (x + y).toBlocks₂₂ ↔ IntM x.toBlocks₂₂ :=
      ⟨fun h => by simpa using (show IntM (x.toBlocks₂₂ + y.toBlocks₂₂) from h).add y22.intM.neg,
        fun h => h.add y22.intM⟩
    unfold parPhi
    have e4 : (δ.comp (Matrix.GeneralLinearGroup.det.comp (KO k a).subtype))⁻¹ = (TypeDatum.full k a).rho δ :=
      (one_mul _).symm
    rw [e4]
    exact if_congr (and_congr e1 (and_congr e2 e3)) ((TypeDatum.full k a).extZ_add hδ x.toBlocks₁₁ y11) rfl

end Local

section Path

theorem isPath_givenPath (m : ℕ) : IsPath (givenPath m) := by
  unfold IsPath givenPath
  rw [List.isChain_append, List.isChain_map, List.isChain_map, List.isChain_reverse, List.isChain_range,
    List.isChain_range]
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  cases m with
  | zero => simp
  | succ m => simp [List.range_succ_eq_map]

theorem mem_givenPath {m : ℕ} {b : Edge} (hb : b ∈ givenPath m) :
    (∃ j < m, b = .theta 0 j) ∨ ∃ i < m, b = .ex i 0 := by
  simp only [givenPath, List.mem_append, List.mem_map, List.mem_reverse, List.mem_range] at hb
  rcases hb with ⟨j, h, rfl⟩ | ⟨i, h, rfl⟩
  exacts [.inl ⟨j, h, rfl⟩, .inr ⟨i, h, rfl⟩]

theorem notMem_inner {m : ℕ} : (0, m) ∉ innerVertices (givenPath m) := by
  cases m with
  | zero => simp [innerVertices, givenPath]
  | succ m =>
    rw [innerVertices, givenPath]
    nth_rewrite 1 [List.range_succ]
    simp

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isAdmissible_of_laws (Γ : Grid k) (s : Assignment) (m : ℕ) (J : Γ.Level)
    (φ : ∀ b : Edge, Matrix (Fin (Γ.rank b.tgt)) (Fin (Γ.rank b.src)) k → ℂ)
    (hθ : ∀ g : Γ.VertexGroup, (∀ Y, g Y ∈ J Y) → g (0, m) = 1 → ∃ c : ℕ → ℂˣ, c 0 = 1 ∧ c m = 1 ∧ ∀ j < m, ∀ x,
      Γ.edgeFactor s g (.theta 0 j) * φ (.theta 0 j) (Γ.moveArgs s g x _) = (c j / c (j + 1) : ℂˣ) * φ (.theta 0 j) (x _))
    (hX : ∀ g : Γ.VertexGroup, (∀ Y, g Y ∈ J Y) → ∀ i < m, ∀ x,
      Γ.edgeFactor s g (.ex i 0) * φ (.ex i 0) (Γ.moveArgs s g x _) = φ (.ex i 0) (x _)) :
    Γ.IsAdmissible s (givenPath m) J (Γ.lines₂ (givenPath m) φ) := by
  intro X hX' u hu
  have hg : ∀ Y, (Pi.mulSingle X u : Γ.VertexGroup) Y ∈ J Y := fun Y => by
    by_cases hY : Y = X
    · subst hY; simpa using hu
    · simp [hY, one_mem]
  have hm : (Pi.mulSingle X u : Γ.VertexGroup) (0, m) = 1 :=
    Pi.mulSingle_eq_of_ne (by rintro rfl; exact notMem_inner hX') _
  generalize (Pi.mulSingle X u : Γ.VertexGroup) = g at hg hm
  obtain ⟨c, h0, h1, hc⟩ := hθ g hg hm
  funext x
  simp only [Grid.pathAct, Grid.lines₂, ← List.prod_map_mul]
  simp only [givenPath, List.map_append, List.map_map, List.prod_append, List.map_reverse, List.prod_reverse,
    Function.comp_def]
  congr 1
  · rw [List.map_congr_left fun j hj => hc j (List.mem_range.1 hj) x, List.prod_map_mul]
    have : ((List.range m).map fun j => ((c j / c (j + 1) : ℂˣ) : ℂ)).prod = 1 := by
      have h2 := congrArg (Units.coeHom ℂ) (List.prod_range_div' m c)
      rwa [map_list_prod, List.map_map, h0, h1, div_one, map_one] at h2
    rw [this, one_mul]
  · rw [List.map_congr_left fun j hj => hX g hg j (List.mem_range.1 hj) x]

end Path

section Global

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}

theorem isEquiv_val (w : Pl D.host.E) :
    (valuation (Kw w)).IsEquiv (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))) :=
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  ValuativeRel.isEquiv _ _

theorem isUnram_loc {χ : HChar D.host.E} {w : Pl D.host.E} (h : χ.UnrAt w) : IsUnram (χ.loc w) :=
  fun x hx => h x ((isEquiv_val w).eq_one_iff_eq_one.1 hx)

theorem condLE_loc {χ : HChar D.host.E} {w : Pl D.host.E} {n e : ℕ} (h : χ.LevelLe w n) (he : n ≤ e) :
    CondLE (unifAt w) e (χ.loc w) := fun x hx => by
  refine h x ((isEquiv_val w).eq_one_iff_eq_one.1 hx.1) (((isEquiv_val w) _ _).1 hx.2 |>.trans ?_)
  have h1 : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  rw [Units.val_pow_eq_pow_val, map_pow, h1, ← WithZero.exp_nsmul, WithZero.exp_le_exp]
  simp only [smul_neg, nsmul_eq_mul, mul_one]
  omega

theorem not_over_of_mem_Q (hL : L.Is μ₀) {t : T} {w : Pl D.host.E} (hw : w ∈ L.Q t) (i : Fin 2) :
    ((D.host.g i : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h => by
  obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := hL.Q_pl t w hw
  have h1 : ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]
    exact card_nsmul_eq_zero'
  obtain ⟨a, b, hab⟩ : IsCoprime ((q : ℕ) : 𝓞 D.host.E) ((D.host.g i : ℕ) : 𝓞 D.host.E) :=
    ((Nat.coprime_primes hq (D.host.g_prime i)).2 (hne i)).cast
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h)))

theorem over_of_mem_Pg (hL : L.Is μ₀) {w : Pl D.host.E} (hw : w ∈ L.Pg) :
    ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
  obtain ⟨i, hi⟩ := (hL.Pg w).1 hw
  have h := L.C.P.pb_over i
  rw [← show w.under (𝓞 D.host.K) = _ from hi] at h
  exact ⟨i, by simpa using (Ideal.mem_comap.1 h)⟩

variable {G : GridData L sc} {t : T} {w : Pl D.host.E}

theorem under_mem_and_place_above_eq_of_mem (hw : w ∈ G.pl.W0) : w.under (𝓞 D.host.F) ∈ G.pl.S0 ∧ G.pl.w (w.under (𝓞 D.host.F)) = w := by
  classical
  obtain ⟨v, hv, rfl⟩ : ∃ v ∈ G.pl.S0, G.pl.w v = w := by simpa [Places.W0] using hw
  rw [G.pl.under_w hv]
  exact ⟨hv, rfl⟩

theorem mem_locPl : w ∈ locPl G t ↔ w ∈ G.pl.W0 ∨ w ∈ L.Q t := by simp [locPl]

theorem eq_of_mem_Q (hw : w ∈ L.Q t) (h : w.under (𝓞 D.host.F) ∈ G.pl.S0) : w = G.pl.w (w.under (𝓞 D.host.F)) :=
  G.pl.w_Q t w hw ((G.pl.mem_S0_of_sum_eq.1 h).resolve_left (G.pl.levelPlace_ne_basePlace t w hw))

theorem xi_unr (hL : L.Is μ₀) (hw : w ∈ G.pl.W0) (hQ : w ∉ L.Q t) : IsUnram ((L.xiH t).loc w) := by
  refine isUnram_loc (by_contra fun h => ?_)
  obtain h | ⟨P, hP, h⟩ := (hL.Q_ram t w).1 h
  · exact hQ h
  · obtain ⟨h1, h2⟩ := under_mem_and_place_above_eq_of_mem hw
    have e : w.under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := by
      rw [(GlobalTheory.IdemSupport.isConjPl_iff P w).1 h, GlobalTheory.IdemSupport.under_cP]
    rw [e] at h1 h2
    exact hQ (h2 ▸ eq_of_mem_Q hP h1 ▸ hP)

theorem muBase_unr (hL : L.Is μ₀) (hw : w ∈ locPl G t) (hP : w ∉ L.Pg) (j : ℕ) : IsUnram ((muBase L j).loc w) := by
  have key : ∀ i, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun i h => by
    rcases mem_locPl.1 hw with hw | hw
    · refine hP ((under_mem_and_place_above_eq_of_mem hw).2 ▸ G.pl.w_g _ i (Ideal.mem_comap.2 ?_))
      simpa using h
    · exact not_over_of_mem_Q hL hw i h
  rcases j with _ | j
  · exact fun _ _ => rfl
  · rw [muBase]
    split_ifs with h
    · exact isUnram_loc ((L.C.isMu0 ⟨j, h⟩).unr w key)
    · exact fun _ _ => rfl

theorem chi_condLE (hw : w ∈ locPl G t) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ D.R.m) :
    CondLE (unifAt w) (cosExp G w) ((G.ch.chiH i).loc w) := by
  by_cases h : w ∈ G.pl.W0
  · rw [cosExp, if_pos h]
    by_cases h0 : w.under (𝓞 D.host.F) = G.pl.v0
    · exact condLE_loc (G.ch.lev0 i h1 h2 w h0).1 (G.pl.depth_pos sc _)
    · refine condLE_loc (G.ch.lev1 i h1 h2 w ((G.pl.mem_S0_of_sum_eq.1 (under_mem_and_place_above_eq_of_mem h).1).resolve_left h0)).1 ?_
      rw [Places.depth, if_neg h0]
  · refine condLE_of_isUnram _ _ (isUnram_loc (G.ch.unr i h1 h2 w fun h' => h ?_))
    classical
    rw [eq_of_mem_Q ((mem_locPl.1 hw).resolve_left h) h']
    unfold Places.W0
    convert Finset.mem_image_of_mem _ h'

variable (L t) in

theorem stepFn_periodic (hL : L.Is μ₀) (w : Pl D.host.E) (j : ℕ) :
    (∀ x, stepFn L t w j x ≠ 0 → IntM x) ∧ ∀ x y, MaxM y → stepFn L t w j (x + y) = stepFn L t w j x := by
  unfold stepFn
  split_ifs
  · exact ⟨fun x hx i l => by simpa using TypeDatum.intM_of_Phi_ne_zero _ _ hx ((ixSucc _ _ j).symm i) l,
      fun x y hy => TypeDatum.Phi_add _ (isTame_muBase w _) (x.submatrix (ixSucc _ _ j) id)
        (y := y.submatrix (ixSucc _ _ j) id) fun _ _ => hy _ _⟩
  · exact parPhi_periodic fun x hx => by rw [MonoidHom.inv_apply, isTame_loc (hL.xi_tame t w) x hx, inv_one]
  · refine ⟨fun x hx => by_contra fun h => hx (Set.indicator_of_notMem h _), fun x y hy => ?_⟩
    refine Set.indicator_eq_indicator ⟨fun h => ?_, fun h => IntM.add h hy.intM⟩ rfl
    simpa using IntM.add h hy.intM.neg

theorem exists_types (hL : L.Is μ₀) (hw : w ∈ locPl G t) :
    ∃ P : ∀ j, TypeDatum (Kw w) (Ix (Fin D.R.r) (Fin D.R.t) j), (∀ j, (P j).J = stepGroup L t w j) ∧
      (∀ j, ∃ ν : (Kw w)ˣ →* ℂˣ, (∀ x : (Kw w)ˣ, valuation (Kw w) (x : Kw w) = 1 →
        (locGrid G t w).mu (j + 1) x = (ν x)⁻¹) ∧ HasTypes ν (P j).toLevel (P (j + 1)).toLevel (stepFn L t w j)) ∧
      (∀ g, (P 0).lam g = 1) ∧ (w ∉ G.pl.W0 → KO (Kw w) _ ≤ (P 0).J) := by
  have hmu : ∀ j x, (locGrid G t w).mu j x = (muBase L j).loc w x * (L.xiH t).loc w x := fun _ _ => rfl
  unfold stepGroup stepFn
  split_ifs with hP hQ
  · have hQ : w ∉ L.Q t := fun h => (over_of_mem_Pg hL hP).elim fun i hi => not_over_of_mem_Q hL h i hi
    have h0 : w ∈ G.pl.W0 := (mem_locPl.1 hw).resolve_right hQ
    exact ⟨fun j => (TypeDatum.principal (Kw w) (Fin D.R.r)).iter (Fin D.R.t) (fun c => ((muBase L c).loc w)⁻¹)
      (isTame_muBase w) j, fun _ => rfl, fun j => ⟨_, fun x hx => by simp [hmu, xi_unr hL h0 hQ x hx],
        TypeDatum.hasTypes_iterPhi _ _ _ j⟩, fun _ => rfl, fun h => absurd h0 h⟩
  · have hδ : IsTame ((L.xiH t).loc w)⁻¹ := fun x hx => by
      rw [MonoidHom.inv_apply, isTame_loc (hL.xi_tame t w) x hx, inv_one]
    refine ⟨fun j => parahoric (Fin D.R.r) (Fin j × Fin D.R.t) _ hδ, fun _ => rfl, fun j => ⟨_, fun x hx => ?_,
      hasTypes_parPhi hδ (ν := 1) fun _ _ => rfl⟩, fun g => ?_, fun _ g hg => mem_parahoric.2 ⟨hg, fun i => i.1.elim0⟩⟩
    · simp [hmu, muBase_unr hL hw hP _ x hx]
    · rw [parahoric_lam g 1 (Matrix.ext fun i => i.1.elim0), map_one, map_one]
  · exact ⟨fun j => TypeDatum.full _ _, fun _ => rfl, fun j => ⟨1, fun x hx => by
      simp [hmu, muBase_unr hL hw hP _ x hx, xi_unr hL ((mem_locPl.1 hw).resolve_right hQ) hQ x hx], hasTypes_vacuum⟩,
      fun _ => rfl, fun _ => le_rfl⟩

theorem int_frames {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b : ℕ}
    {Λ : Submodule (𝓞 E) (Fin b → E)} {Λ' : Submodule (𝓞 E) (Fin a → E)} {β : GL (Fin b) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {β' : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : IsFrame β Λ) (h' : IsFrame β' Λ') {y : Matrix (Fin a) (Fin b) E}
    (hy : ∀ x ∈ Λ, y *ᵥ x ∈ Λ') (i : Fin a) (j : Fin b) :
    ((β'⁻¹).val * y.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) * β.val) i j ∈ Formalism.L2.Herm.intAf F E := by
  have key : ∀ x ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      y.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      exact Submodule.subset_span ⟨_, hy x hx, funext fun i => RingHom.map_mulVec _ y x i⟩
    | zero => rw [mulVec_zero]; exact zero_mem _
    | add x z _ _ hx hz => rw [mulVec_add]; exact add_mem hx hz
    | smul r x _ hx =>
      have := mulVec_smul (y.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) r.1 x
      exact (show _ *ᵥ (r • x) = r • _ from this) ▸ Submodule.smul_mem _ r hx
  have h1 := (h (β.val *ᵥ Pi.single j 1)).2 fun l => by
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have h2 := (h' _).1 (key _ h1) i
  rwa [mulVec_mulVec, mulVec_mulVec, mulVec_single_one] at h2

theorem map_frames {A A' : Type} [CommRing A] [CommRing A'] (c : A →+* A') {a b : ℕ} (β' : GL (Fin a) A) (β : GL (Fin b) A)
    (y : Matrix (Fin a) (Fin b) A) (i : Fin a) (j : Fin b) :
    (((GeneralLinearGroup.map c β')⁻¹).val * y.map c * (GeneralLinearGroup.map c β).val) i j =
      c (((β'⁻¹).val * y * β.val) i j) := by
  rw [← Matrix.map_apply (f := c), Matrix.map_mul, Matrix.map_mul]
  rfl

theorem intM_frames {a b : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {β : GL (Fin b) (Formalism.IndefR.Lev.EAf D)}
    {β' : GL (Fin a) (Formalism.IndefR.Lev.EAf D)} (h : IsFrame β Λ) (h' : IsFrame β' Λ') (w : Pl D.host.E) (y : homLat Λ Λ') :
    IntM (((loc w β')⁻¹).val * y.1.map (algebraMap D.host.E (Kw w)) * (loc w β).val) := by
  let ι : D.host.E →+* Formalism.IndefR.Lev.EAf D := Formalism.UG.inclE (F := D.host.F) _
  have hι : ∀ x, cpt w (ι x) = algebraMap D.host.E (Kw w) x := fun x =>
    congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z w) (GlobalTheory.AdeleBaseChange.map_tmul_one (toAd_spec D) x)
  intro i j
  have h2 := (mem_OA_iff _).1 (int_frames h h' y.2 i j) w
  rw [← map_frames, Matrix.map_map, show cpt w ∘ ι = algebraMap D.host.E (Kw w) from funext hι] at h2
  exact (isEquiv_val w).le_one_iff_le_one.2 h2

variable (B : Frames G) (Φ : G.Datum)

theorem intM_coord (hL : L.Is μ₀) {i : ℕ} (hi : i < D.R.m) (y : homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) :
    IntM (B.coord t w (X := (i, 0)) (Y := (i + 1, 0)) ⟨hi.le, Nat.zero_le _⟩ ⟨hi, Nat.zero_le _⟩
      (y.1.map (algebraMap D.host.E (Kw w)))) :=
  fun _ _ => intM_frames (B.isFrame_β hL hi (Nat.zero_le _)) (B.isFrame_β hL hi.le (Nat.zero_le _)) w y _ _

theorem isNatDatum_givenDatum (hL : L.Is μ₀) {b : Edge} (hb : b ∈ givenPath D.R.m) :
    IsNatDatum (unifAt w) (depthAt G w) (givenDatum t w B Φ b) := by
  obtain ⟨j, -, rfl⟩ | ⟨i, hi, rfl⟩ := mem_givenPath hb
  · obtain ⟨h1, h2⟩ := stepFn_periodic L t hL w j
    refine isNatDatum_of_periodic (fun x hx a b => ?_) (fun x y hy => h2 _ (yᵀ.submatrix _ _) fun _ _ => hy _ _)
      (isUnif_unifAt w) (le_max_right _ _)
    simpa using h1 _ hx ((ixFin G t w (j + 1)).symm b) ((ixFin G t w j).symm a)
  · rw [givenDatum, dif_pos hi]
    exact isNatDatum_cosets (intM_coord B hL hi) (isUnif_unifAt w) (le_max_left _ _)

theorem givenLevel_succ {j : ℕ} {P : TypeDatum (Kw w) (Ix (Fin D.R.r) (Fin D.R.t) (j + 1))}
    (hP : P.J = stepGroup L t w (j + 1)) : givenLevel G t w (0, j + 1) = (P.reindex (ixFin G t w (j + 1))).J := by
  rw [givenLevel, ← hP]
  exact Subgroup.map_equiv_eq_comap_symm' _ _

theorem givenLevel_open (hL : L.Is μ₀) (hw : w ∈ locPl G t) (X : ℕ × ℕ) :
    IsOpen (givenLevel G t w X : Set (GL (Fin ((locGrid G t w).rank X)) (Kw w))) ∧ givenLevel G t w X ≤ KO (Kw w) _ := by
  obtain ⟨i, _ | j⟩ := X
  · rw [givenLevel]
    exact ⟨isOpen_glLatCong _, fun g hg => (mem_glLatCong.1 hg).1⟩
  · rcases i with _ | i
    · obtain ⟨P, hP, -⟩ := exists_types hL hw
      rw [givenLevel_succ (hP _)]
      exact ⟨TypeDatum.isOpen _, TypeDatum.le_KO _⟩
    · exact ⟨SplitFlip.isOpen_KO, le_rfl⟩

theorem edgeFactor_eq {g : (locGrid G t w).VertexGroup} (hg : ∀ Y, g Y ∈ KO (Kw w) _) (b : Edge) :
    (locGrid G t w).edgeFactor .one g b = ((locGrid G t w).blockChar b (gdet (g b.src)) : ℂ) *
      (((locGrid G t w).blockChar b (gdet (g b.tgt)))⁻¹ : ℂˣ) := by
  have h : ∀ Y, (locGrid G t w).eta (gdet (g Y)) = 1 := fun Y =>
    isUnram_loc (L.C.isEta.unr w) _ (valuation_gdet_of_mem_KO (hg Y))
  simp only [Grid.edgeFactor, Grid.kappa,
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO (hg _)))]
  simp [h]

theorem row_law (hL : L.Is μ₀) (hw : w ∈ locPl G t) (g : (locGrid G t w).VertexGroup)
    (hg : ∀ Y, g Y ∈ givenLevel G t w Y) (i : ℕ) (hi : i < D.R.m) (x : (locGrid G t w).Args) :
    (locGrid G t w).edgeFactor .one g (.ex i 0) * givenDatum t w B Φ (.ex i 0) ((locGrid G t w).moveArgs .one g x _) =
      givenDatum t w B Φ (.ex i 0) (x _) := by
  have h0 : ∀ l, g (l, 0) ∈ glLatCong (unifAt w ^ cosExp G w) (SplitFlip.stdLat (Kw w) _) := fun l => by
    have := hg (l, 0)
    rwa [givenLevel] at this
  have hc : ∀ l, (locGrid G t w).blockChar (.ex i 0) (gdet (g (l, 0))) = 1 := fun l =>
    chi_condLE hw (by change 1 ≤ D.R.m - i; omega) (Nat.sub_le _ _) _ (gdet_mem_unitCong (h0 l))
  rw [edgeFactor_eq fun Y => (givenLevel_open hL hw Y).2 (hg Y), hc, hc, inv_one, Units.val_one, one_mul, one_mul,
    givenDatum, dif_pos hi]
  exact indicator_cosets_mul (intM_coord B hL hi) (inv_mem (invT_mem_glLatCong (h0 _))) (invT_mem_glLatCong (h0 _)) _

theorem column_law (hL : L.Is μ₀) (hw : w ∈ locPl G t) (g : (locGrid G t w).VertexGroup)
    (hg : ∀ Y, g Y ∈ givenLevel G t w Y) (hm : g (0, D.R.m) = 1) :
    ∃ c : ℕ → ℂˣ, c 0 = 1 ∧ c D.R.m = 1 ∧ ∀ j < D.R.m, ∀ x : (locGrid G t w).Args,
      (locGrid G t w).edgeFactor .one g (.theta 0 j) *
          givenDatum t w B Φ (.theta 0 j) ((locGrid G t w).moveArgs .one g x _) =
        (c j / c (j + 1) : ℂˣ) * givenDatum t w B Φ (.theta 0 j) (x _) := by
  obtain ⟨P, hP, hlaw, h0, hK⟩ := exists_types hL hw
  have hKO : ∀ Y, g Y ∈ KO (Kw w) _ := fun Y => (givenLevel_open hL hw Y).2 (hg Y)
  have hmem : ∀ j, (reGL (ixFin G t w j)).symm (g (0, j)) ∈ (P j).J := by
    rintro (_ | j)
    · by_cases h : w ∈ G.pl.W0
      · refine ((P 0).reindex (ixFin G t w 0)).KOne_le (mem_KOne.2 fun a b => ?_)
        refine ((mem_glLatCong.1 (hg (0, 0))).2 a b).trans_lt ?_
        rw [Units.val_pow_eq_pow_val, map_pow, isUnif_unifAt w, cosExp, if_pos h]
        exact pow_lt_one₀ zero_le uniformizer_lt_one (G.pl.depth_pos sc _).ne'
      · refine hK h (mem_KO.2 ⟨fun a b => intM_of_mem_KO (hKO (0, 0)) _ _, fun a b => ?_⟩)
        rw [← map_inv]
        exact (mem_KO.1 (hKO (0, 0))).2 _ _
    · have := hg (0, j + 1)
      rwa [givenLevel_succ (hP _)] at this
  refine ⟨fun j => (P j).lam ⟨_, hmem j⟩, h0 _, ?_, fun j _ x => ?_⟩
  · rw [← map_one (P D.R.m).lam]
    exact congrArg _ (Subtype.ext (by simp [hm]))
  · obtain ⟨ν, hν, H⟩ := hlaw j
    have e := law_of_hasTypes H ⟨_, hmem j⟩ ⟨_, hmem (j + 1)⟩
      ((x (.theta 0 j))ᵀ.submatrix (ixFin G t w (j + 1)) (ixFin G t w j))
    have hd : ∀ l, gdet ((reGL (ixFin G t w l)).symm (g (0, l))) = gdet (g (0, l)) := fun l =>
      (det_reGL (ixFin G t w l) _).symm.trans (by rw [MulEquiv.apply_symm_apply])
    rw [hd, hd] at e
    rw [edgeFactor_eq hKO, Grid.blockChar, hν _ (valuation_gdet_of_mem_KO (hKO _)),
      hν _ (valuation_gdet_of_mem_KO (hKO _)), inv_inv, mul_comm ((_ : ℂˣ) : ℂ)]
    refine Eq.trans (congrArg _ (congrArg (stepFn L t w j) ?_)) e
    rw [← map_inv, reGL_symm_val, reGL_symm_val, submatrix_mul_equiv, submatrix_mul_equiv]
    simp only [Grid.moveArgs, Assignment.read, invT_val, invT_inv_val, transpose_mul, transpose_transpose,
      Matrix.mul_assoc]

theorem givenStage_isAdmissible {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀)
    {G : GridData L sc} (B : Frames G) (t : T) (Φ : G.Datum) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    (givenStage t w B Φ).IsAdmissible .one (unifAt w) (depthAt G w) :=
  ⟨isPath_givenPath _, fun X _ => givenLevel_open hL hw X,
    Grid.isTensor_pureTensor _ _ _ _ _ fun _ hb => isNatDatum_givenDatum B Φ hL hb,
    isAdmissible_of_laws _ _ _ _ _ (column_law B Φ hL hw) (row_law B Φ hL hw)⟩

end Global

end GlobalTheory.FunObj.GivenAdm

end
