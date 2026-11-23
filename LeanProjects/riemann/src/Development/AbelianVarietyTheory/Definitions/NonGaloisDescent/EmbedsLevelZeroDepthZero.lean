import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open GlobalTheory.Parabolic (Embeds isIrreducible_of_equiv mem_fixed)

namespace GlobalTheory.LocGL

section General

variable {G M V : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V]

def levelRep (ρ : Representation ℂ G V) {P J : Subgroup G} (hP : P ≤ Subgroup.normalizer (J : Set G)) (q : P →* M)
    (hq : Function.Surjective q) (hk : ∀ p, q p = 1 → (p : G) ∈ J) : Representation ℂ M (fixed ρ J) :=
  descend (onFixed ρ J P.subtype fun p => hP p.2) q hq fun p hp =>
    LinearMap.ext fun v => Subtype.ext (mem_fixed.1 v.2 _ (hk p hp))

theorem levelRep_apply (ρ : Representation ℂ G V) {P J : Subgroup G} (hP : P ≤ Subgroup.normalizer (J : Set G))
    (q : P →* M) (hq : Function.Surjective q) (hk : ∀ p, q p = 1 → (p : G) ∈ J) (p : P) (v : fixed ρ J) :
    (levelRep ρ hP q hq hk (q p) v : V) = ρ p v := by
  rw [levelRep, descend_apply]; rfl

end General

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

variable (n) in

def toKO : GL n 𝒪[k] ≃* KO k n :=
  MonoidHom.ofInjective fun _ _ h => Units.ext (Matrix.ext fun i j =>
    Subtype.ext (congrArg (fun g : GL n k => (g : Matrix n n k) i j) h))

variable (n) in

def redK : KO k n →* GL n 𝓀[k] :=
  (GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k])).comp (toKO k n).symm.toMonoidHom

variable {k}

theorem redK_apply (g : KO k n) (i j : n) : (redK k n g : Matrix n n 𝓀[k]) i j =
    IsLocalRing.residue 𝒪[k] ⟨((g : GL n k) : Matrix n n k) i j, StepData.intM_of_mem_KO g.2 i j⟩ := by
  obtain ⟨u, rfl⟩ := (toKO k n).surjective g
  simp only [redK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rfl

theorem redK_eq_iff (g : KO k n) (i j : n) (x : 𝒪[k]) :
    (redK k n g : Matrix n n 𝓀[k]) i j = IsLocalRing.residue 𝒪[k] x ↔
      valuation k (((g : GL n k) : Matrix n n k) i j - x) < 1 := by
  rw [redK_apply, StepData.residue_eq_iff_lt]

theorem redK_eq_zero_iff (g : KO k n) (i j : n) :
    (redK k n g : Matrix n n 𝓀[k]) i j = 0 ↔ valuation k (((g : GL n k) : Matrix n n k) i j) < 1 := by
  rw [redK_apply, StepData.residue_eq_zero_iff_lt]

theorem redK_surjective : Function.Surjective (redK k n) := by
  intro x
  choose A hA using fun i j => IsLocalRing.residue_surjective (R := 𝒪[k]) ((x : Matrix n n 𝓀[k]) i j)
  have h1 : (IsLocalRing.residue 𝒪[k]).mapMatrix (Matrix.of A) = x := Matrix.ext hA
  have hd : IsUnit (Matrix.of A).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, h1]
    exact (GeneralLinearGroup.det x).ne_zero
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hd
  refine ⟨toKO k n u, Units.ext ?_⟩
  simp only [redK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rw [← h1, ← hu]; rfl

theorem redK_eq_one_iff (g : KO k n) : redK k n g = 1 ↔ (g : GL n k) ∈ KOne k n := by
  obtain ⟨u, rfl⟩ := (toKO k n).surjective g
  simp only [redK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  refine ⟨fun h => ⟨u, h, rfl⟩, ?_⟩
  rintro ⟨u', h, e⟩
  obtain rfl : u' = u := (toKO k n).injective (Subtype.ext e)
  exact h

def levelPre (H : Subgroup (GL n 𝓀[k])) : Subgroup (GL n k) := (H.comap (redK k n)).map (KO k n).subtype

theorem mem_levelPre {H : Subgroup (GL n 𝓀[k])} {g : GL n k} :
    g ∈ levelPre H ↔ ∃ h : g ∈ KO k n, redK k n ⟨g, h⟩ ∈ H :=
  ⟨by rintro ⟨x, hx, rfl⟩; exact ⟨x.2, hx⟩, fun ⟨h, hg⟩ => ⟨⟨g, h⟩, hg, rfl⟩⟩

theorem coe_mem_levelPre {H : Subgroup (GL n 𝓀[k])} (g : KO k n) : (g : GL n k) ∈ levelPre H ↔ redK k n g ∈ H :=
  mem_levelPre.trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨g.2, h⟩⟩

theorem levelPre_le_KO (H : Subgroup (GL n 𝓀[k])) : levelPre H ≤ KO k n := fun _ h => (mem_levelPre.1 h).1

theorem KOne_le_levelPre (H : Subgroup (GL n 𝓀[k])) : KOne k n ≤ levelPre H := fun g h =>
  mem_levelPre.2 ⟨StepData.KOne_le_KO h, by rw [(redK_eq_one_iff ⟨g, _⟩).2 h]; exact one_mem H⟩

theorem levelPre_bot : levelPre (⊥ : Subgroup (GL n 𝓀[k])) = KOne k n :=
  le_antisymm (fun _ h => let ⟨_, h⟩ := mem_levelPre.1 h; (redK_eq_one_iff _).1 h) (KOne_le_levelPre _)

theorem levelPre_top : levelPre (⊤ : Subgroup (GL n 𝓀[k])) = KO k n :=
  le_antisymm (levelPre_le_KO _) fun _ h => mem_levelPre.2 ⟨h, trivial⟩

theorem levelPre_mono {H H' : Subgroup (GL n 𝓀[k])} (h : H ≤ H') : levelPre H ≤ levelPre H' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem isOpen_levelPre (H : Subgroup (GL n 𝓀[k])) : IsOpen (levelPre H : Set (GL n k)) :=
  Subgroup.isOpen_mono (KOne_le_levelPre H) StepData.isOpen_KOne

theorem isCompact_levelPre (H : Subgroup (GL n 𝓀[k])) : IsCompact (levelPre H : Set (GL n k)) :=
  SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (isOpen_levelPre H)) (levelPre_le_KO H)

theorem levelPre_le_normalizer {H U : Subgroup (GL n 𝓀[k])} (h : H ≤ Subgroup.normalizer (U : Set (GL n 𝓀[k]))) :
    levelPre H ≤ Subgroup.normalizer (levelPre U : Set (GL n k)) := by
  have key : ∀ p ∈ levelPre H, ∀ u ∈ levelPre U, p * u * p⁻¹ ∈ levelPre U := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨u, hu, rfl⟩
    refine ⟨p * u * p⁻¹, ?_, rfl⟩
    show redK k n (p * u * p⁻¹) ∈ U
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (h hp) _).1 hu
  intro p hp
  refine Subgroup.mem_normalizer_iff.2 fun u => ⟨key p hp u, fun h => ?_⟩
  simpa [mul_assoc] using key _ (inv_mem hp) _ h

theorem KO_le_normalizer : KO k n ≤ Subgroup.normalizer (KOne k n : Set (GL n k)) := by
  rw [← levelPre_top, ← levelPre_bot]
  exact levelPre_le_normalizer (by rw [Subgroup.normalizer_eq_top])

def levelZero (π : Representation ℂ (GL n k) V) : Representation ℂ (GL n 𝓀[k]) (fixed π (KOne k n)) :=
  levelRep π KO_le_normalizer (redK k n) redK_surjective fun g => (redK_eq_one_iff g).1

@[simp] theorem levelZero_apply (π : Representation ℂ (GL n k) V) (g : KO k n) (v : fixed π (KOne k n)) :
    (levelZero π (redK k n g) v : V) = π g v := levelRep_apply _ _ _ _ _ g v

def levelZeroMap {π : Representation ℂ (GL n k) V} {σ : Representation ℂ (GL n k) W} (f : π.IntertwiningMap σ) :
    (levelZero π).IntertwiningMap (levelZero σ) where
  toLinearMap := f.toLinearMap.restrict fun v hv => mem_fixed.2 fun u hu => by
    rw [f.toLinearMap_apply, ← f.isIntertwining, mem_fixed.1 hv u hu]
  isIntertwining' x := by
    obtain ⟨g, rfl⟩ := redK_surjective x
    refine LinearMap.ext fun v => Subtype.ext ?_
    show f (levelZero π _ v : V) = (levelZero σ _ _ : W)
    rw [levelZero_apply, levelZero_apply, f.isIntertwining]; rfl

def inflateK (ρ : Representation ℂ (GL n 𝓀[k]) W) : Representation ℂ (KO k n) W := ρ.comp (redK k n)

variable (k)

def parahoric (e : (Σ a, m a) ≃ n) : Subgroup (GL n k) := levelPre (parab 𝓀[k] e)

def proRad (e : (Σ a, m a) ≃ n) : Subgroup (GL n k) := levelPre (unipRad 𝓀[k] e)

variable (m) in

def leviK : Subgroup (Levi k m) := Subgroup.pi Set.univ fun a => KO k (m a)

variable (m) in

def leviKOne : Subgroup (Levi k m) := Subgroup.pi Set.univ fun a => KOne k (m a)

def jMinus (e : (Σ a, m a) ≃ n) : Subgroup (GL n k) := unipRadLower k e ⊓ KOne k n

def jLevi (e : (Σ a, m a) ≃ n) : Subgroup (GL n k) := (leviKOne k m).map (leviEmb k e)

def jPlus (e : (Σ a, m a) ≃ n) : Subgroup (GL n k) := unipRad k e ⊓ KO k n

def parahoricProj (e : (Σ a, m a) ≃ n) : parahoric k e →* Levi 𝓀[k] m :=
  (leviProj 𝓀[k] e).comp (((redK k n).comp (Subgroup.inclusion (levelPre_le_KO _))).codRestrict _
    fun p => (mem_levelPre.1 p.2).2)

variable (m) in

def redLevi : leviK k m →* Levi 𝓀[k] m :=
  MonoidHom.pi fun a => (redK k (m a)).comp
    (((Pi.evalMonoidHom (fun a => GL (m a) k) a).comp (leviK k m).subtype).codRestrict _ fun g => g.2 a trivial)

variable {k}

omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in

theorem mem_parahoric {e : (Σ a, m a) ≃ n} {g : GL n k} : g ∈ parahoric k e ↔ g ∈ KO k n ∧
    ∀ a b (i : m a) (j : m b), b < a → valuation k ((g : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩)) < 1 := by
  simp only [parahoric, mem_levelPre, mem_parab_iff, redK_eq_zero_iff, exists_prop]

theorem mem_proRad {e : (Σ a, m a) ≃ n} {g : GL n k} : g ∈ proRad k e ↔ g ∈ parahoric k e ∧
    ∀ a (i j : m a), valuation k ((g : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) - (1 : Matrix (m a) (m a) k) i j) < 1 := by
  have key : ∀ (h : g ∈ KO k n) a (i j : m a),
      (redK k n ⟨g, h⟩ : Matrix n n 𝓀[k]) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) 𝓀[k]) i j ↔
      valuation k ((g : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) - (1 : Matrix (m a) (m a) k) i j) < 1 := by
    intro h a i j
    by_cases hij : i = j
    · subst hij
      simpa using redK_eq_iff ⟨g, h⟩ (e ⟨a, i⟩) (e ⟨a, i⟩) 1
    · simpa [hij] using redK_eq_zero_iff ⟨g, h⟩ (e ⟨a, i⟩) (e ⟨a, j⟩)
  simp only [proRad, parahoric, mem_levelPre, mem_unipRad, key]
  exact ⟨fun ⟨h, h1, h2⟩ => ⟨⟨h, h1⟩, h2⟩, fun ⟨⟨h, h1⟩, h2⟩ => ⟨h, h1, h2⟩⟩

theorem proRad_le_parahoric (e : (Σ a, m a) ≃ n) : proRad k e ≤ parahoric k e :=
  levelPre_mono (unipRad_le_parab _ e)

theorem parahoric_le_normalizer (e : (Σ a, m a) ≃ n) :
    parahoric k e ≤ Subgroup.normalizer (proRad k e : Set (GL n k)) :=
  levelPre_le_normalizer (parab_le_normalizer _ e)

theorem parahoricProj_eq_one_iff (e : (Σ a, m a) ≃ n) (p : parahoric k e) :
    parahoricProj k e p = 1 ↔ (p : GL n k) ∈ proRad k e :=
  (coe_mem_unipRad _ _).symm.trans (coe_mem_levelPre (H := unipRad 𝓀[k] e) ⟨(p : GL n k), levelPre_le_KO _ p.2⟩).symm

theorem parahoricProj_surjective (e : (Σ a, m a) ≃ n) : Function.Surjective (parahoricProj k e) := by
  intro x
  obtain ⟨g, hg⟩ := redK_surjective (leviEmb 𝓀[k] e x)
  refine ⟨⟨g, (coe_mem_levelPre g).2 (hg ▸ leviEmb_mem_parab _ e x)⟩, ?_⟩
  exact (congrArg (leviProj 𝓀[k] e) (Subtype.ext hg)).trans (leviProj_leviEmb 𝓀[k] e x)

omit [Fintype α] [LinearOrder α] in

theorem redLevi_apply (g : leviK k m) (a : α) : redLevi k m g a = redK k (m a) ⟨g.1 a, g.2 a trivial⟩ := rfl

omit [Fintype α] [LinearOrder α] in

theorem redLevi_surjective : Function.Surjective (redLevi k m) := fun x => by
  choose g hg using fun a => redK_surjective (x a)
  exact ⟨⟨fun a => g a, fun a _ => (g a).2⟩, funext hg⟩

omit [Fintype α] [LinearOrder α] in

theorem redLevi_eq_one_iff (g : leviK k m) : redLevi k m g = 1 ↔ (g : Levi k m) ∈ leviKOne k m :=
  ⟨fun h a _ => (redK_eq_one_iff ⟨g.1 a, g.2 a trivial⟩).1 (congrFun h a),
    fun h => funext fun a => (redK_eq_one_iff ⟨g.1 a, g.2 a trivial⟩).2 (h a trivial)⟩

omit [Fintype α] [LinearOrder α] in

theorem leviK_le_normalizer : leviK k m ≤ Subgroup.normalizer (leviKOne k m : Set (Levi k m)) := fun g hg =>
  Subgroup.mem_normalizer_iff.2 fun u => forall₂_congr fun a _ =>
    Subgroup.mem_normalizer_iff.1 (KO_le_normalizer (hg a trivial)) (u a)

omit [LinearOrder α] in

theorem leviEmb_mem_KO (e : (Σ a, m a) ≃ n) {g : Levi k m} (hg : g ∈ leviK k m) : leviEmb k e g ∈ KO k n := by
  have key : ∀ {g : Levi k m}, g ∈ leviK k m → StepData.IntM (leviEmb k e g).val := by
    intro g hg i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    by_cases h : a = b
    · subst h
      rw [leviEmb_apply_same]
      exact StepData.intM_of_mem_KO (hg a trivial) i j
    · rw [leviEmb_apply_ne k e g h]; exact zero_mem _
  exact StepData.mem_KO.2 ⟨key hg, by rw [← map_inv]; exact key (inv_mem hg)⟩

omit [LinearOrder α] in

theorem redK_leviEmb (e : (Σ a, m a) ≃ n) (g : leviK k m) :
    redK k n ⟨leviEmb k e g, leviEmb_mem_KO e g.2⟩ = leviEmb 𝓀[k] e (redLevi k m g) := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  by_cases h : a = b
  · subst h
    rw [leviEmb_apply_same, redLevi_apply, redK_apply, redK_apply]
    simp only [leviEmb_apply_same]
  · rw [leviEmb_apply_ne _ e _ h, redK_eq_zero_iff, leviEmb_apply_ne _ e _ h]
    simp

theorem leviEmb_mem_parahoric (e : (Σ a, m a) ≃ n) (g : leviK k m) : leviEmb k e g ∈ parahoric k e :=
  mem_levelPre.2 ⟨leviEmb_mem_KO e g.2, redK_leviEmb e g ▸ leviEmb_mem_parab _ e _⟩

theorem parahoricProj_leviEmb (e : (Σ a, m a) ≃ n) (g : leviK k m) :
    parahoricProj k e ⟨leviEmb k e g, leviEmb_mem_parahoric e g⟩ = redLevi k m g := by
  rw [← leviProj_leviEmb 𝓀[k] e (redLevi k m g)]
  exact congrArg (leviProj 𝓀[k] e) (Subtype.ext (redK_leviEmb e g))

theorem KOne_le_proRad (e : (Σ a, m a) ≃ n) : KOne k n ≤ proRad k e := KOne_le_levelPre _

omit [LinearOrder α] in

theorem jLevi_le_KOne (e : (Σ a, m a) ≃ n) : jLevi k e ≤ KOne k n := by
  rintro _ ⟨g, hg, rfl⟩
  have h : g ∈ leviK k m := fun a _ => StepData.KOne_le_KO (hg a trivial)
  refine (redK_eq_one_iff ⟨_, leviEmb_mem_KO e h⟩).1 ?_
  rw [redK_leviEmb e ⟨g, h⟩, (redLevi_eq_one_iff _).2 hg, map_one]

theorem jMinus_le_proRad (e : (Σ a, m a) ≃ n) : jMinus k e ≤ proRad k e := inf_le_right.trans (KOne_le_proRad e)

theorem jLevi_le_proRad (e : (Σ a, m a) ≃ n) : jLevi k e ≤ proRad k e := (jLevi_le_KOne e).trans (KOne_le_proRad e)

theorem jPlus_le_proRad (e : (Σ a, m a) ≃ n) : jPlus k e ≤ proRad k e := fun g hg =>
  mem_proRad.2 ⟨mem_parahoric.2 ⟨hg.2, fun a b i j h => by
    rw [mem_parab_iff.1 (mem_unipRad.1 hg.1).1 a b i j h]; simp⟩, fun a i j => by
    rw [(mem_unipRad.1 hg.1).2]; simp⟩

def parahoricInv (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n k) V) :
    Representation ℂ (Levi 𝓀[k] m) (fixed π (proRad k e)) :=
  levelRep π (parahoric_le_normalizer e) (parahoricProj k e) (parahoricProj_surjective e)
    fun p => (parahoricProj_eq_one_iff e p).1

@[simp] theorem parahoricInv_apply (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n k) V) (p : parahoric k e)
    (v : fixed π (proRad k e)) : (parahoricInv e π (parahoricProj k e p) v : V) = π p v :=
  levelRep_apply _ _ _ _ _ p v

@[simp] theorem parahoricInv_redLevi (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n k) V) (g : leviK k m)
    (v : fixed π (proRad k e)) : (parahoricInv e π (redLevi k m g) v : V) = π (leviEmb k e g) v := by
  rw [← parahoricProj_leviEmb e, parahoricInv_apply]

def leviLevelZero {α : Type} {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (τ : Representation ℂ (Levi k m) W) : Representation ℂ (Levi 𝓀[k] m) (fixed τ (leviKOne k m)) :=
  levelRep τ leviK_le_normalizer (redLevi k m) redLevi_surjective fun g => (redLevi_eq_one_iff g).1

omit [Fintype α] [LinearOrder α] in

@[simp] theorem leviLevelZero_apply (τ : Representation ℂ (Levi k m) W) (g : leviK k m) (v : fixed τ (leviKOne k m)) :
    (leviLevelZero τ (redLevi k m g) v : W) = τ g v := levelRep_apply _ _ _ _ _ g v

def toJacquet (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n k) V) :
    (parahoricInv e π).IntertwiningMap (leviLevelZero (jacU e π)) where
  toLinearMap := (twKer π (unipRad k e) 1).mkQ.restrict fun v hv => mem_fixed.2 fun g hg =>
    congrArg Submodule.Quotient.mk (mem_fixed.1 hv _ (jLevi_le_proRad e ⟨g, hg, rfl⟩))
  isIntertwining' x := by
    obtain ⟨g, rfl⟩ := redLevi_surjective x
    refine LinearMap.ext fun v => Subtype.ext ?_
    refine Eq.trans ?_ (leviLevelZero_apply (jacU e π) g _).symm
    exact congrArg Submodule.Quotient.mk (parahoricInv_redLevi e π g v)

@[simp] theorem toJacquet_apply (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n k) V) (v : fixed π (proRad k e)) :
    (toJacquet e π v : Jacquet π (unipRad k e)) = Submodule.Quotient.mk (v : V) := rfl

theorem detChar_of_mem_KO {ν : kˣ →* ℂˣ} (hν : IsUnram ν) {g : GL n k} (hg : g ∈ KO k n) : detChar n ν g = 1 :=
  hν _ (StepData.valuation_det_of_mem_KO hg)

theorem deltaHalf_of_mem_leviK {g : Levi k m} (hg : g ∈ leviK k m) : deltaHalf k m g = 1 := by
  rw [deltaHalf_apply]
  exact Finset.prod_eq_one fun a _ => detChar_of_mem_KO (isUnram_absPow k _) (hg a trivial)

section Two

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def parahoricInv₂ (e : a ⊕ b ≃ n) (π : Representation ℂ (GL n k) V) :
    Representation ℂ (GL a 𝓀[k] × GL b 𝓀[k]) (fixed π (proRad k (two e))) :=
  (parahoricInv (two e) π).comp (leviTwo 𝓀[k] a b).toMonoidHom

variable (k a b) in

def redProd : (KO k a).prod (KO k b) →* GL a 𝓀[k] × GL b 𝓀[k] :=
  ((redK k a).prodMap (redK k b)).comp ((KO k a).prodEquiv (KO k b)).toMonoidHom

theorem redProd_surjective : Function.Surjective (redProd k a b) := fun x => by
  obtain ⟨g, hg⟩ := redK_surjective x.1
  obtain ⟨h, hh⟩ := redK_surjective x.2
  exact ⟨⟨(g, h), g.2, h.2⟩, Prod.ext hg hh⟩

def prodLevelZero (τ : Representation ℂ (GL a k × GL b k) W) :
    Representation ℂ (GL a 𝓀[k] × GL b 𝓀[k]) (fixed τ ((KOne k a).prod (KOne k b))) :=
  levelRep τ (P := (KO k a).prod (KO k b))
    (fun g hg => Subgroup.mem_normalizer_iff.2 fun u => and_congr
      (Subgroup.mem_normalizer_iff.1 (KO_le_normalizer hg.1) u.1)
      (Subgroup.mem_normalizer_iff.1 (KO_le_normalizer hg.2) u.2))
    (redProd k a b) redProd_surjective fun g hg =>
      ⟨(redK_eq_one_iff ⟨g.1.1, g.2.1⟩).1 (congrArg Prod.fst hg), (redK_eq_one_iff ⟨g.1.2, g.2.2⟩).1 (congrArg Prod.snd hg)⟩

@[simp] theorem prodLevelZero_apply (τ : Representation ℂ (GL a k × GL b k) W) (g : (KO k a).prod (KO k b))
    (v : fixed τ ((KOne k a).prod (KOne k b))) : (prodLevelZero τ (redProd k a b g) v : W) = τ g v :=
  levelRep_apply _ _ _ _ _ g v

@[simp] theorem parahoricInv₂_apply (e : a ⊕ b ≃ n) (π : Representation ℂ (GL n k) V) (g : (KO k a).prod (KO k b))
    (v : fixed π (proRad k (two e))) : (parahoricInv₂ e π (redProd k a b g) v : V) = π (emb₂ k e g) v := by
  have hg : leviTwo k a b g ∈ leviK k (Two a b) := by
    rintro (_ | _) -
    exacts [g.2.1, g.2.2]
  have h : leviTwo 𝓀[k] a b (redProd k a b g) = redLevi k _ ⟨_, hg⟩ := by
    funext x; cases x <;> rfl
  show (parahoricInv (two e) π (leviTwo 𝓀[k] a b (redProd k a b g)) v : V) = _
  rw [h, parahoricInv_redLevi]; rfl

def toJacquet₂ (e : a ⊕ b ≃ n) (π : Representation ℂ (GL n k) V) :
    (parahoricInv₂ e π).IntertwiningMap (prodLevelZero (jacU₂ e π)) where
  toLinearMap := (twKer π (unipRad k (two e)) 1).mkQ.restrict fun v hv => mem_fixed.2 fun g hg =>
    congrArg Submodule.Quotient.mk (mem_fixed.1 hv _ (jLevi_le_proRad (two e) ⟨leviTwo k a b g, by
      rintro (_ | _) -
      exacts [hg.1, hg.2], rfl⟩))
  isIntertwining' x := by
    obtain ⟨g, rfl⟩ := redProd_surjective x
    refine LinearMap.ext fun v => Subtype.ext ?_
    refine Eq.trans ?_ (prodLevelZero_apply (jacU₂ e π) g _).symm
    exact congrArg Submodule.Quotient.mk (parahoricInv₂_apply e π g v)

@[simp] theorem toJacquet₂_apply (e : a ⊕ b ≃ n) (π : Representation ℂ (GL n k) V) (v : fixed π (proRad k (two e))) :
    (toJacquet₂ e π v : Jacquet π (unipRad k (two e))) = Submodule.Quotient.mk (v : V) := rfl

end Two

section Finite

variable {R : Type} [Field R] {N h : ℕ} {d : Fin h → ℕ}

theorem unipRad_eq_of_le (e : (Σ a, m a) ≃ Fin N) {c : Fin N → ℕ} (hc : ∀ i j, c j ≤ c i ↔ blk e j ≤ blk e i) :
    unipRad R e = FiniteGL.unipRadical R c := by
  ext g
  rw [mem_unipRad, FiniteGL.mem_unipRadical, mem_parab_iff]
  simp only [hc, Matrix.sub_apply, sub_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at hij
    rcases hij.eq_or_lt with rfl | h
    · rw [h2]; simp [Matrix.one_apply]
    · rw [h1 a b i j h, Matrix.one_apply_ne fun e' => h.ne' (congrArg Sigma.fst (e.injective e'))]
  · intro hg
    refine ⟨fun a b i j h => ?_, fun a i j => ?_⟩
    · rw [hg _ _ (by simpa using h.le), Matrix.one_apply_ne fun e' => h.ne' (congrArg Sigma.fst (e.injective e'))]
    · rw [hg _ _ (by simp)]; simp [Matrix.one_apply]

theorem unipRad_eq_unipRadical (e : (Σ a, Fin (d a)) ≃ Fin N) :
    unipRad R e = FiniteGL.unipRadical R (Parabolic.blockOf e) := unipRad_eq_of_le e fun _ _ => Iff.rfl

theorem unipRad_two_eq {r t : ℕ} (hN : r + t = N) :
    unipRad R (two (stdSum hN)) = FiniteGL.unipRadical R (FiniteGL.twoBlocks N r) := by
  refine unipRad_eq_of_le _ fun i j => ?_
  obtain ⟨⟨_ | _, i⟩, rfl⟩ := (two (stdSum hN)).surjective i <;>
    obtain ⟨⟨_ | _, j⟩, rfl⟩ := (two (stdSum hN)).surjective j <;>
    simp only [blk_apply] <;> simp [FiniteGL.twoBlocks]

theorem coe_leviEquiv_symm (e : (Σ a, Fin (d a)) ≃ Fin N) (x : Levi R fun a => Fin (d a)) :
    ((Parabolic.leviEquiv e).symm x : GL (Fin N) R) = leviEmb R e x := by
  obtain ⟨g, rfl⟩ := (Parabolic.leviEquiv e).surjective x
  rw [MulEquiv.symm_apply_apply]
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  by_cases h : a = b
  · subst h; rw [leviEmb_apply_same]; rfl
  · rw [leviEmb_apply_ne R e _ h]
    exact g.2 _ _ (by simpa [Fin.val_inj] using h)

theorem coe_leviTwo_symm {r t : ℕ} (hN : r + t = N) {c : Fin N → ℕ} (hc : Parabolic.IsTwoBlock r c)
    (x : GL (Fin r) R × GL (Fin t) R) :
    ((Parabolic.leviTwo hN hc).symm x : GL (Fin N) R) = emb₂ R (stdSum hN) x :=
  Units.ext (val_emb₂ R (stdSum hN) x).symm

def finInd (e : (Σ a, Fin (d a)) ≃ Fin N) (σ : Representation ℂ (Levi R fun a => Fin (d a)) W) :=
  Parabolic.hcInd (Parabolic.blockOf e) (σ.comp (Parabolic.leviEquiv e).toMonoidHom)

def finRes (e : (Σ a, Fin (d a)) ≃ Fin N) (κ : Representation ℂ (GL (Fin N) R) V) :
    Representation ℂ (Levi R fun a => Fin (d a)) (fixed κ (FiniteGL.unipRadical R (Parabolic.blockOf e))) :=
  (Parabolic.hcRes (Parabolic.blockOf e) κ).comp (Parabolic.leviEquiv e).symm.toMonoidHom

def fixedLevelPre (π : Representation ℂ (GL n k) V) {U U' : Subgroup (GL n 𝓀[k])} (hU : U = U') :
    fixed π (levelPre U) ≃ₗ[ℂ] fixed (levelZero π) U' where
  toFun v := ⟨⟨v, mem_fixed.2 fun g hg => mem_fixed.1 v.2 g (KOne_le_levelPre U hg)⟩, mem_fixed.2 fun x hx => by
    obtain ⟨g, rfl⟩ := redK_surjective x
    exact Subtype.ext ((levelZero_apply π g _).trans (mem_fixed.1 v.2 _ ((coe_mem_levelPre g).2 (hU ▸ hx))))⟩
  invFun w := ⟨w.1, mem_fixed.2 fun g hg => by
    obtain ⟨h, hg⟩ := mem_levelPre.1 hg
    exact (levelZero_apply π ⟨g, h⟩ w.1).symm.trans (congrArg Subtype.val (mem_fixed.1 w.2 _ (hU ▸ hg)))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def parahoricInvEquiv (e : (Σ a, Fin (d a)) ≃ Fin N) (π : Representation ℂ (GL (Fin N) k) V) :
    (parahoricInv e π).Equiv (finRes e (levelZero π)) :=
  .mk (fixedLevelPre π (unipRad_eq_unipRadical e)) fun x => by
    obtain ⟨g, rfl⟩ := redLevi_surjective x
    refine LinearMap.ext fun v => Subtype.ext (Subtype.ext ?_)
    refine (parahoricInv_redLevi e π g v).trans ?_
    show _ = (levelZero π ((Parabolic.leviEquiv e).symm (redLevi k _ g) : GL (Fin N) 𝓀[k]) _ : V)
    rw [coe_leviEquiv_symm, ← redK_leviEmb, levelZero_apply]; rfl

def parahoricInv₂Equiv {r t : ℕ} (hN : r + t = N) (π : Representation ℂ (GL (Fin N) k) V) :
    (parahoricInv₂ (stdSum hN) π).Equiv
      (Parabolic.twoRes hN (Parabolic.isTwoBlock_twoBlocks N r) (levelZero π)) :=
  .mk (fixedLevelPre π (unipRad_two_eq hN)) fun x => by
    obtain ⟨g, hg⟩ := redLevi_surjective (leviTwo 𝓀[k] _ _ x)
    refine LinearMap.ext fun v => Subtype.ext (Subtype.ext ?_)
    show (parahoricInv (two (stdSum hN)) π (leviTwo 𝓀[k] _ _ x) v : V) =
      (levelZero π ((Parabolic.leviTwo hN (Parabolic.isTwoBlock_twoBlocks N r)).symm x : GL (Fin N) 𝓀[k]) _ : V)
    rw [coe_leviTwo_symm, emb₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hg, ← redK_leviEmb, levelZero_apply,
      parahoricInv_redLevi]; rfl

end Finite

variable (k) in

abbrev unitIncl : 𝒪[k]ˣ →* kˣ := Units.map (algebraMap 𝒪[k] k).toMonoidHom

variable (k) in

abbrev unitRes : 𝒪[k]ˣ →* 𝓀[k]ˣ := Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom

theorem valuation_eq_one_iff {x : kˣ} : valuation k (x : k) = 1 ↔ ∃ u, unitIncl k u = x := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one
      (x := ⟨x, h.le⟩) |>.2 h
    exact ⟨u, Units.ext (congrArg Subtype.val hu)⟩
  · rintro ⟨u, rfl⟩
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit

def IsTameLift (χ' : kˣ →* ℂˣ) (χ : 𝓀[k]ˣ →* ℂˣ) : Prop := ∀ u : 𝒪[k]ˣ, χ' (unitIncl k u) = χ (unitRes k u)

theorem IsTameLift.mul {χ' ψ' : kˣ →* ℂˣ} {χ ψ : 𝓀[k]ˣ →* ℂˣ} (h : IsTameLift χ' χ) (h' : IsTameLift ψ' ψ) :
    IsTameLift (χ' * ψ') (χ * ψ) := fun u => by rw [MonoidHom.mul_apply, MonoidHom.mul_apply, h, h']

theorem IsTameLift.detChar_eq {χ' : kˣ →* ℂˣ} {χ : 𝓀[k]ˣ →* ℂˣ} (h : IsTameLift χ' χ) (g : KO k n) :
    detChar n χ' g = detChar n χ (redK k n g) := by
  obtain ⟨u, rfl⟩ := (toKO k n).surjective g
  simp only [redK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, detChar_apply]
  convert h (GeneralLinearGroup.det u) using 2
  · exact Units.ext ((algebraMap 𝒪[k] k).map_det u.val).symm
  · exact Units.ext ((IsLocalRing.residue 𝒪[k]).map_det u.val).symm

theorem IsTameLift.isTame {χ' : kˣ →* ℂˣ} {χ : 𝓀[k]ˣ →* ℂˣ} (h : IsTameLift χ' χ) : IsTame χ' := fun x hx => by
  have h1 : valuation k (x : k) = 1 := by
    simpa using (valuation k).map_one_add_of_lt hx
  obtain ⟨u, rfl⟩ := valuation_eq_one_iff.1 h1
  have : unitRes k u = 1 := Units.ext (((StepData.residue_eq_iff_lt (u : 𝒪[k]) 1).2 hx).trans (map_one _))
  rw [h, this, map_one]

theorem isSmoothChar_of_isTame {χ' : kˣ →* ℂˣ} (h : IsTame χ') : IsSmoothChar χ' := by
  have ho : IsOpen {x : kˣ | valuation k ((x : k) - 1) < 1} := by
    refine IsOpen.preimage (f := fun x : kˣ => (x : k) - 1) (t := {y | valuation k y < 1}) (by fun_prop) ?_
    simpa using (valuation k).isOpen_ball 1
  exact Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (ho.mem_nhds (by simp)) h)

variable (k) in

theorem exists_uniformizer : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (K := k) (uniformizer k)
  exact ⟨Units.mk0 x fun h => uniformizer_ne_zero (by rw [← hx, h, map_zero]), hx⟩

theorem exists_isTameLift (χ : 𝓀[k]ˣ →* ℂˣ) {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (c : ℂˣ) :
    ∃ χ' : kˣ →* ℂˣ, IsTameLift χ' χ ∧ χ' ϖ = c := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  let p : kˣ →* kˣ := MonoidHom.id _ / (zpowersHom kˣ ϖ).comp o
  have hp : ∀ x, p x = x / ϖ ^ ord k x := fun _ => rfl
  have hinj : Function.Injective (unitIncl k) := Units.map_injective Subtype.val_injective
  have hm : ∀ x, p x ∈ (unitIncl k).range := fun x => by
    have h1 : o (x / ϖ ^ ord k x) = 1 := by
      rw [map_div, map_zpow, show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd (ord_eq_one hϖ), ← ofAdd_zsmul,
        smul_eq_mul, mul_one]
      exact div_self' _
    exact valuation_eq_one_iff.1 (ord_eq_zero_iff.1 (ofAdd_eq_one.1 h1))
  let r : kˣ →* 𝒪[k]ˣ := (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (p.codRestrict _ hm)
  have hr : ∀ x, unitIncl k (r x) = p x := fun x =>
    congrArg Subtype.val ((MonoidHom.ofInjective hinj).apply_symm_apply ⟨p x, hm x⟩)
  refine ⟨χ.comp ((unitRes k).comp r) * unrChar k c, fun u => ?_, ?_⟩
  · have hu := valuation_eq_one_iff.2 ⟨u, rfl⟩
    have : r (unitIncl k u) = u := hinj (by rw [hr, hp, ord_eq_zero hu, zpow_zero, div_one])
    rw [MonoidHom.mul_apply, isUnram_unrChar k c _ hu, mul_one, MonoidHom.comp_apply, MonoidHom.comp_apply, this]
  · have : r ϖ = 1 := hinj (by rw [hr, hp, ord_eq_one hϖ, zpow_one, div_self', map_one])
    rw [MonoidHom.mul_apply, unrChar_uniformizer k c hϖ, MonoidHom.comp_apply, MonoidHom.comp_apply, this]
    simp

variable (k n) in

def zkHom : kˣ × KO k n →* GL n k :=
  (GeneralLinearGroup.scalar n).noncommCoprod (KO k n).subtype fun z g => GeneralLinearGroup.scalar_commute z (g : GL n k)

variable (k n) in

def ZK : Subgroup (GL n k) := (zkHom k n).range

theorem mem_ZK {g : GL n k} : g ∈ ZK k n ↔ ∃ z : kˣ, ∃ x ∈ KO k n, GeneralLinearGroup.scalar n z * x = g :=
  ⟨fun ⟨y, h⟩ => ⟨y.1, y.2, y.2.2, h⟩, fun ⟨z, x, hx, h⟩ => ⟨(z, ⟨x, hx⟩), h⟩⟩

theorem KO_le_ZK : KO k n ≤ ZK k n := fun g hg => mem_ZK.2 ⟨1, g, hg, by simp⟩

theorem scalar_mem_ZK (z : kˣ) : GeneralLinearGroup.scalar n z ∈ ZK k n := mem_ZK.2 ⟨z, 1, one_mem _, mul_one _⟩

def ExtendsCentral (ω : kˣ →* ℂˣ) (ρ : Representation ℂ (GL n 𝓀[k]) W) : Prop :=
  ∀ (z : kˣ) (h : GeneralLinearGroup.scalar n z ∈ KO k n) (w : W), ρ (redK k n ⟨_, h⟩) w = (ω z : ℂ) • w

theorem scalar_mem_KO (u : 𝒪[k]ˣ) : GeneralLinearGroup.scalar n (unitIncl k u) ∈ KO k n :=
  ⟨GeneralLinearGroup.scalar n u, by
    ext i j
    show algebraMap 𝒪[k] k (Matrix.scalar n (u : 𝒪[k]) i j) = Matrix.scalar n ((u : 𝒪[k]) : k) i j
    by_cases h : i = j
    · simp only [h, Matrix.scalar_apply, diagonal_apply_eq]; rfl
    · simp [h]⟩

theorem redK_scalar (u : 𝒪[k]ˣ) :
    redK k n ⟨_, scalar_mem_KO u⟩ = GeneralLinearGroup.scalar n (unitRes k u) := by
  ext i j
  by_cases h : i = j
  · subst h
    refine ((redK_eq_iff _ i i u).2 ?_).trans (by simp)
    show valuation k (Matrix.scalar n ((u : 𝒪[k]) : k) i i - _) < 1
    simp
  · refine ((redK_eq_zero_iff _ i j).2 ?_).trans (by simp [h])
    simp [h]

theorem extendsCentral_iff [Nonempty n] {ω : kˣ →* ℂˣ} {ρ : Representation ℂ (GL n 𝓀[k]) W} :
    ExtendsCentral ω ρ ↔ ∀ (u : 𝒪[k]ˣ) (w : W),
      ρ (GeneralLinearGroup.scalar n (unitRes k u)) w = (ω (unitIncl k u) : ℂ) • w := by
  refine ⟨fun h u w => by rw [← redK_scalar]; exact h _ _ w, fun h z hz w => ?_⟩
  obtain ⟨i⟩ := ‹Nonempty n›
  have h1 : valuation k (z : k) ≤ 1 := by
    have h0 : (z : k) ∈ 𝒪[k] := by simpa using (StepData.mem_KO.1 hz).1 i i
    exact h0
  have h2 : valuation k ((z⁻¹ : kˣ) : k) ≤ 1 := by
    have := (StepData.mem_KO.1 hz).2 i i
    rw [← map_inv, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at this
    exact this
  rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
  obtain ⟨u, rfl⟩ := valuation_eq_one_iff.1 (le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 (by simp))).1 h2))
  rw [redK_scalar, h]

theorem IsTameLift.extendsCentral [Nonempty n] {ω : kˣ →* ℂˣ} {ω₀ : 𝓀[k]ˣ →* ℂˣ} (h : IsTameLift ω ω₀)
    {ρ : Representation ℂ (GL n 𝓀[k]) W} (hρ : HasCentralChar ρ ω₀) : ExtendsCentral ω ρ :=
  extendsCentral_iff.2 fun u w => by rw [hρ, h]

theorem exists_hasCentralChar {R : Type} [CommRing R] [FiniteDimensional ℂ W] {ρ : Representation ℂ (GL n R) W}
    (h : ρ.IsIrreducible) : ∃ ω, HasCentralChar ρ ω := by
  have := Model.nontrivial_of_isIrreducible h
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
  have key : ∀ z : Rˣ, ∃ c : ℂ, ∀ w, ρ (GeneralLinearGroup.scalar n z) w = c • w := fun z => by
    obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).2
      ⟨ρ (GeneralLinearGroup.scalar n z), fun g => by
        rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, GeneralLinearGroup.scalar_commute]⟩
    exact ⟨c, fun w => (congrArg (fun f : ρ.IntertwiningMap ρ => f w) hc).symm⟩
  choose c hc using key
  refine ⟨MonoidHom.toHomUnits ⟨⟨c, smul_left_injective ℂ hw₀ ?_⟩, fun x y => smul_left_injective ℂ hw₀ ?_⟩, hc⟩
  · simp [← hc]
  · simp only [← hc, mul_smul, map_mul, Module.End.mul_apply]

def extZK (ρ : Representation ℂ (GL n 𝓀[k]) W) (ω : kˣ →* ℂˣ) (h : ExtendsCentral ω ρ) :
    Representation ℂ (ZK k n) W :=
  descend (twist ((inflateK ρ).comp (MonoidHom.snd _ _)) (ω.comp (MonoidHom.fst _ _))) (zkHom k n).rangeRestrict
    (zkHom k n).rangeRestrict_surjective fun ⟨z, g⟩ hg => by
      have h1 : GeneralLinearGroup.scalar n z * g = 1 := congrArg Subtype.val hg
      have h2 : GeneralLinearGroup.scalar n z⁻¹ = g := by rw [map_inv]; exact inv_eq_of_mul_eq_one_right h1
      obtain ⟨g, hg'⟩ := g
      subst h2
      ext w
      show (ω z : ℂ) • ρ (redK k n ⟨_, hg'⟩) w = w
      rw [h, smul_smul]; simp

theorem extZK_apply (ρ : Representation ℂ (GL n 𝓀[k]) W) (ω : kˣ →* ℂˣ) (h : ExtendsCentral ω ρ) (z : kˣ) (g : KO k n)
    (x : ZK k n) (hx : GeneralLinearGroup.scalar n z * g = x) (w : W) :
    extZK ρ ω h x w = (ω z : ℂ) • ρ (redK k n g) w := by
  obtain rfl : (zkHom k n).rangeRestrict (z, g) = x := Subtype.ext hx
  exact LinearMap.congr_fun (descend_apply _ (zkHom k n).rangeRestrict _ _ (z, g)) w

@[simp] theorem extZK_KO (ρ : Representation ℂ (GL n 𝓀[k]) W) (ω : kˣ →* ℂˣ) (h : ExtendsCentral ω ρ) (g : KO k n)
    (w : W) : extZK ρ ω h ⟨g, KO_le_ZK g.2⟩ w = ρ (redK k n g) w := by
  rw [extZK_apply ρ ω h 1 g _ (by simp)]; simp

@[simp] theorem extZK_scalar (ρ : Representation ℂ (GL n 𝓀[k]) W) (ω : kˣ →* ℂˣ) (h : ExtendsCentral ω ρ) (z : kˣ)
    (w : W) : extZK ρ ω h ⟨_, scalar_mem_ZK z⟩ w = (ω z : ℂ) • w := by
  rw [extZK_apply ρ ω h z 1 _ (by simp)]; simp

def DepthZeroSp (ρ : Representation ℂ (GL n 𝓀[k]) W) (ω : kˣ →* ℂˣ) (h : ExtendsCentral ω ρ) : Type :=
  cIndSpace (ZK k n) (extZK ρ ω h)

instance (ρ : Representation ℂ (GL n 𝓀[k]) W) (ω : kˣ →* ℂˣ) (h : ExtendsCentral ω ρ) :
    AddCommGroup (DepthZeroSp ρ ω h) := inferInstanceAs (AddCommGroup (cIndSpace (ZK k n) (extZK ρ ω h)))

instance (ρ : Representation ℂ (GL n 𝓀[k]) W) (ω : kˣ →* ℂˣ) (h : ExtendsCentral ω ρ) :
    Module ℂ (DepthZeroSp ρ ω h) := inferInstanceAs (Module ℂ (cIndSpace (ZK k n) (extZK ρ ω h)))

def depthZero (ρ : Representation ℂ (GL n 𝓀[k]) W) (ω : kˣ →* ℂˣ) (h : ExtendsCentral ω ρ) :
    Representation ℂ (GL n k) (DepthZeroSp ρ ω h) :=
  cInd (ZK k n) (extZK ρ ω h)

@[simp] theorem depthZero_apply (ρ : Representation ℂ (GL n 𝓀[k]) W) (ω : kˣ →* ℂˣ) (h : ExtendsCentral ω ρ)
    (g x : GL n k) (f : DepthZeroSp ρ ω h) : (depthZero ρ ω h g f).1.1.1 x = f.1.1.1 (x * g) := rfl

theorem isSmooth_depthZero (ρ : Representation ℂ (GL n 𝓀[k]) W) (ω : kˣ →* ℂˣ) (h : ExtendsCentral ω ρ) :
    IsSmooth (depthZero ρ ω h) := fun f => by
  have : {g | depthZero ρ ω h g f = f} = {g | smInd (ZK k n) (extZK ρ ω h) g f.1 = f.1} := by
    ext g; exact Subtype.ext_iff
  rw [this]; exact isSmooth_smoothRep _ _

theorem hasCentralChar_depthZero (ρ : Representation ℂ (GL n 𝓀[k]) W) (ω : kˣ →* ℂˣ) (h : ExtendsCentral ω ρ) :
    HasCentralChar (depthZero ρ ω h) ω := fun z f => by
  refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => ?_)))
  rw [depthZero_apply, ← GeneralLinearGroup.scalar_commute]
  exact (f.1.1.2 ⟨_, scalar_mem_ZK z⟩ x).trans (extZK_scalar ρ ω h z _)

open Classical in

def canonFun (ρ : Representation ℂ (GL n 𝓀[k]) W) (ω : kˣ →* ℂˣ) (h : ExtendsCentral ω ρ) (w : W) (g : GL n k) : W :=
  if hg : g ∈ ZK k n then extZK ρ ω h ⟨g, hg⟩ w else 0

theorem canonFun_mul (ρ : Representation ℂ (GL n 𝓀[k]) W) (ω : kˣ →* ℂˣ) (h : ExtendsCentral ω ρ) (w : W)
    (g : GL n k) (x : ZK k n) : canonFun ρ ω h w (g * x) = canonFun ρ ω h (extZK ρ ω h x w) g := by
  unfold canonFun
  by_cases hg : g ∈ ZK k n
  · rw [dif_pos hg, dif_pos (mul_mem hg x.2), ← Module.End.mul_apply, ← map_mul]; rfl
  · rw [dif_neg hg, dif_neg fun h' => hg ((Subgroup.mul_mem_cancel_right _ x.2).1 h')]

def canon (ρ : Representation ℂ (GL n 𝓀[k]) W) (ω : kˣ →* ℂˣ) (h : ExtendsCentral ω ρ) :
    (extZK ρ ω h).IntertwiningMap ((depthZero ρ ω h).comp (ZK k n).subtype) where
  toFun w := ⟨⟨⟨canonFun ρ ω h w, fun x g => by
      unfold canonFun
      by_cases hg : g ∈ ZK k n
      · rw [dif_pos hg, dif_pos (mul_mem x.2 hg), ← Module.End.mul_apply, ← map_mul]; rfl
      · rw [dif_neg hg, dif_neg fun h' => hg ((Subgroup.mul_mem_cancel_left _ x.2).1 h'), map_zero]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset (StepData.isOpen_KOne.mem_nhds (one_mem _)) fun u hu => by
      refine Subtype.ext (funext fun g => ?_)
      have h1 := StepData.KOne_le_KO hu
      refine (canonFun_mul ρ ω h w g ⟨u, KO_le_ZK h1⟩).trans ?_
      rw [extZK_KO ρ ω h ⟨u, h1⟩, (redK_eq_one_iff ⟨u, h1⟩).2 hu, map_one]; rfl)⟩,
    {1}, isCompact_singleton, fun g hg => ⟨g, by_contra fun h' => hg (dif_neg h'), 1, rfl, (mul_one g).symm⟩⟩
  map_add' v w := Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => by
    show canonFun ρ ω h (v + w) g = canonFun ρ ω h v g + canonFun ρ ω h w g
    unfold canonFun; split_ifs <;> simp)))
  map_smul' c w := Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => by
    show canonFun ρ ω h (c • w) g = c • canonFun ρ ω h w g
    unfold canonFun; split_ifs <;> simp)))
  isIntertwining' x := LinearMap.ext fun w => Subtype.ext (Subtype.ext (Subtype.ext (funext fun g =>
    (canonFun_mul ρ ω h w g x).symm)))

theorem canon_injective (ρ : Representation ℂ (GL n 𝓀[k]) W) (ω : kˣ →* ℂˣ) (h : ExtendsCentral ω ρ) :
    Function.Injective (canon ρ ω h) := fun v w e => by
  have h1 : canonFun ρ ω h v 1 = canonFun ρ ω h w 1 := congrArg (fun f => f.1.1.1 1) e
  have h2 : ∀ v, canonFun ρ ω h v 1 = v := fun v => (dif_pos (one_mem _)).trans (LinearMap.congr_fun (map_one _) v)
  rwa [h2, h2] at h1

def conjK (ρ : Representation ℂ (GL n 𝓀[k]) W) (g : GL n k) :
    Representation ℂ ↥(KO k n ⊓ (KO k n).comap (MulAut.conj g⁻¹).toMonoidHom) W :=
  (inflateK ρ).comp (((MulAut.conj g⁻¹).toMonoidHom.comp (Subgroup.subtype _)).codRestrict _ fun x => x.2.2)

def resK (ρ : Representation ℂ (GL n 𝓀[k]) W) (g : GL n k) :
    Representation ℂ ↥(KO k n ⊓ (KO k n).comap (MulAut.conj g⁻¹).toMonoidHom) W :=
  (inflateK ρ).comp (Subgroup.inclusion inf_le_left)

def InertEquiv (π : Representation ℂ (GL n k) V) (σ : Representation ℂ (GL n k) W) : Prop :=
  ∃ ν : kˣ →* ℂˣ, IsUnram ν ∧ Nonempty (σ.Equiv (twist π (detChar n ν)))

theorem isUnram_mul {ν μ : kˣ →* ℂˣ} (h : IsUnram ν) (h' : IsUnram μ) : IsUnram (ν * μ) := fun x hx => by
  rw [MonoidHom.mul_apply, h x hx, h' x hx, one_mul]

theorem isUnram_inv {ν : kˣ →* ℂˣ} (h : IsUnram ν) : IsUnram ν⁻¹ := fun x hx => by
  rw [MonoidHom.inv_apply, h x hx, inv_one]

theorem InertEquiv.of_equiv {π : Representation ℂ (GL n k) V} {σ : Representation ℂ (GL n k) W} (e : π.Equiv σ) :
    InertEquiv π σ :=
  ⟨1, fun _ _ => rfl, ⟨by rw [show detChar n (1 : kˣ →* ℂˣ) = 1 from rfl, twist_one]; exact e.symm⟩⟩

theorem InertEquiv.symm {π : Representation ℂ (GL n k) V} {σ : Representation ℂ (GL n k) W} (h : InertEquiv π σ) :
    InertEquiv σ π := by
  obtain ⟨ν, hν, ⟨e⟩⟩ := h
  refine ⟨ν⁻¹, isUnram_inv hν, ⟨?_⟩⟩
  have e' := twistEquiv e (detChar n ν⁻¹)
  rw [twist_twist, show detChar n ν⁻¹ * detChar n ν = 1 from MonoidHom.ext fun g => by simp, twist_one] at e'
  exact e'.symm

theorem InertEquiv.trans {X : Type} [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (GL n k) V}
    {σ : Representation ℂ (GL n k) W} {τ : Representation ℂ (GL n k) X} (h : InertEquiv π σ) (h' : InertEquiv σ τ) :
    InertEquiv π τ := by
  obtain ⟨ν, hν, ⟨e⟩⟩ := h
  obtain ⟨μ, hμ, ⟨f⟩⟩ := h'
  have e' := twistEquiv e (detChar n μ)
  rw [twist_twist] at e'
  exact ⟨μ * ν, isUnram_mul hμ hν, ⟨f.trans e'⟩⟩

def levelZeroTwist (π : Representation ℂ (GL n k) V) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) :
    (levelZero (twist π (detChar n ν))).Equiv (levelZero π) :=
  .mk (LinearEquiv.ofEq _ _ (Submodule.ext fun v => by
      simp only [mem_fixed]
      exact forall₂_congr fun u hu => by rw [twist_apply, detChar_of_mem_KO hν (StepData.KOne_le_KO hu)]; simp))
    fun x => by
      obtain ⟨g, rfl⟩ := redK_surjective x
      refine LinearMap.ext fun v => Subtype.ext ((levelZero_apply _ g v).trans ((levelZero_apply π g _).trans ?_).symm)
      rw [twist_apply, detChar_of_mem_KO hν g.2]; simp

theorem InertEquiv.levelZero {π : Representation ℂ (GL n k) V} {σ : Representation ℂ (GL n k) W} (h : InertEquiv π σ) :
    Nonempty ((levelZero σ).Equiv (levelZero π)) := by
  obtain ⟨ν, hν, ⟨e⟩⟩ := h
  refine ⟨(equivOfBijective (levelZeroMap e.toIntertwiningMap) ⟨fun v w h =>
    Subtype.ext (e.toLinearEquiv.injective (congrArg Subtype.val h)), fun w =>
    ⟨levelZeroMap e.symm.toIntertwiningMap w, Subtype.ext (e.apply_symm_apply _)⟩⟩).trans (levelZeroTwist π hν)⟩

example {χ' : kˣ →* ℂˣ} {χ : 𝓀[k]ˣ →* ℂˣ} (h : IsTameLift χ' χ) :
    ExtendsCentral (χ' ^ Fintype.card n) (detRep n χ) := fun z hz w => by
  show ofChar _ _ _ = _
  have : GeneralLinearGroup.det (GeneralLinearGroup.scalar n z) = z ^ Fintype.card n := by
    ext; simp [GeneralLinearGroup.scalar]
  rw [ofChar_apply, ← h.detChar_eq, detChar_apply, this]
  simp

end GlobalTheory.LocGL
