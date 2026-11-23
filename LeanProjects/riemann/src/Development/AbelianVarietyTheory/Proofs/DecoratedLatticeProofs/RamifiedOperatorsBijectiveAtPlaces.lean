import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorBijectiveFiniteTranslationCombinStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFramePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.AllBij

section Comb

variable {G : Type} [Group G]

def act (c : G →₀ ℂ) (F : G → ℂ) : G → ℂ := c.sum fun g x => x • rTrans g F

theorem act_apply (c : G →₀ ℂ) (F : G → ℂ) (y : G) : act c F y = c.sum fun g x => x * F (y * g) := by
  simp [act, Finsupp.sum, Finset.sum_apply, rTrans]

def cmul (c d : G →₀ ℂ) : G →₀ ℂ := c.sum fun g x => d.sum fun h y => Finsupp.single (g * h) (x * y)

theorem act_cmul (c d : G →₀ ℂ) (F : G → ℂ) : act (cmul c d) F = act c (act d F) := by
  funext y
  rw [act_apply, act_apply, cmul, Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul])]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul]), act_apply, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun h _ => ?_
  rw [Finsupp.sum_single_index (by simp)]
  simp [mul_assoc]

theorem act_single_one (F : G → ℂ) : act (Finsupp.single 1 1) F = F := by
  funext y; rw [act_apply, Finsupp.sum_single_index (by simp)]; simp

theorem act_mapDomain {H : Type} (f : H → G) (c : H →₀ ℂ) (F : G → ℂ) :
    act (Finsupp.mapDomain f c) F = c.sum fun h x => x • rTrans (f h) F := by
  rw [act, Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]

theorem cmul_mem {S : Subgroup G} {c d : G →₀ ℂ} (hc : ∀ g, c g ≠ 0 → g ∈ S) (hd : ∀ g, d g ≠ 0 → g ∈ S) :
    ∀ g, cmul c d g ≠ 0 → g ∈ S := by
  classical
  intro g hg
  obtain ⟨a, ha, hga⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum (Finsupp.mem_support_iff.2 hg))
  obtain ⟨b, hb, hgb⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hga)
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hgb)]
  exact S.mul_mem (hc a (Finsupp.mem_support_iff.1 ha)) (hd b (Finsupp.mem_support_iff.1 hb))

theorem mapDomain_mem {H : Type} {S : Subgroup G} (f : H → G) (hf : ∀ h, f h ∈ S) (c : H →₀ ℂ) :
    ∀ g, Finsupp.mapDomain f c g ≠ 0 → g ∈ S := by
  classical
  intro g hg
  obtain ⟨h, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support (Finsupp.mem_support_iff.2 hg))
  exact hf h

def actL (c : G →₀ ℂ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun := act c
  map_add' F F' := by funext y; simp [act_apply, mul_add, Finsupp.sum_add]
  map_smul' r F := by funext y; simp [act_apply, Finsupp.mul_sum, mul_left_comm]

end Comb

end GlobalTheory.FinPl.AllBij

namespace GlobalTheory.FinPl.AllBij

open GlobalTheory.FinPl

variable {D : D7}

theorem isContAut_act {V : HSp D} (c : GA D V →₀ ℂ) {F : GA D V → ℂ} (hF : IsContAut V F) : IsContAut V (act c F) := by
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · rw [act_apply, act_apply]
    exact Finsupp.sum_congr fun h _ => by rw [mul_assoc, hF.1 γ hγ]
  · have : act c F = fun y => c.sum fun g x => x * F (y * g) := funext (act_apply c F)
    rw [this]
    exact continuous_finsetSum _ fun h _ => continuous_const.mul (hF.2.comp (continuous_id.mul continuous_const))

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem rep_eq (β : Frame p S n) (g : GL n k) (F : GA D S → ℂ) : β.rep g F = rTrans (β.gl g) F := rfl

theorem sum_rep_eq (β : Frame p S n) (c : GL n k →₀ ℂ) (F : GA D S → ℂ) :
    (c.sum fun g a => a • β.rep g F) = act (Finsupp.mapDomain β.gl c) F := by
  rw [act_mapDomain]; rfl

theorem ramAt_act (β : Frame p S n) (P : Pair k n) (c : GA D S →₀ ℂ)
    (hc : ∀ x, c x ≠ 0 → ∀ g, x * β.gl g = β.gl g * x) {φ₀ : GA D S → ℂ} (hφ : RamAt β P φ₀) :
    RamAt β P (act c φ₀) := by
  obtain ⟨φ, ⟨heq, hram, hcont⟩, rfl⟩ := hφ
  refine ⟨fun Q => actL c (φ Q), ⟨?_, ?_, fun Q => isContAut_act c (hcont Q)⟩, rfl⟩
  · intro g Q
    show act c (φ (g • Q)) = β.rep g (act c (φ Q))
    rw [heq g Q]
    funext y
    rw [rep_eq, rep_eq, act_apply]
    show _ = act c (φ Q) (y * β.gl g)
    rw [act_apply]
    refine Finsupp.sum_congr fun x hx => ?_
    simp only [rTrans]
    rw [mul_assoc, hc x (Finsupp.mem_support_iff.1 hx) g, mul_assoc]
  · let _ := Fintype.ofFinite 𝓀[k]ˣ
    refine (mem_Mram _).2 fun Q => ?_
    have h0 := (mem_Mram φ).1 hram Q
    rw [← map_sum, h0, map_zero]

end Frames

end GlobalTheory.FinPl.AllBij

namespace GlobalTheory.FinPl.AllBij

open GlobalTheory.FinPl

variable {D : D7}

theorem congGrp_mono (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro g hg
  simp only [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at hg ⊢
  have key : ∀ x : GL (Fin V.rank) (AE D), Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) x =
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor h) (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) x) := by
    intro x; ext i j; simp [Ideal.Quotient.factor_mk]
  rw [key, hg, map_one]

theorem idAt_mono {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : idAt D P ≤ idAt D P' := by
  intro a ha
  simp only [idAt, Ideal.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun hw => w.2 (h _ hw)⟩⟩

theorem idAt_le_idOff {v w : Pl D} (h : v ≠ w) : idAt D (· = v) ≤ idOff D (· = w) := by
  intro a ha
  simp only [idAt, idOff, Ideal.mem_inf, Submodule.mem_iInf] at ha ⊢
  intro u
  have hu : u.1 = w := u.2
  exact ha.2 ⟨u.1, fun e => h (e.symm.trans hu)⟩

theorem grpAt_comm (V : HSp D) {v w : Pl D} (h : v ≠ w) {x y : GA D V} (hx : x ∈ grpAt V (· = w))
    (hy : y ∈ grpAt V (· = v)) : x * y = y * x :=
  (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = w)).2 V |>.2.1 x hx y (congGrp_mono V (idAt_le_idOff h) hy)

end GlobalTheory.FinPl.AllBij

namespace GlobalTheory.FinPl.AllBij

open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {A S : HSp D}

theorem gl_mem {p₀ : SplitPt D k} (β : Frame p₀ A n) (g : GL n k) : β.gl g ∈ grpAt A (· = p₀.v) :=
  ((GlobalTheory.T.splitPlaceHermitianFrame_properties D k p₀ A n β).1 _).2 ⟨g, rfl⟩

theorem sAll_cons (a : PairDat p A S n) (q : Unif k) (χ : ι → AddChar 𝓀[k] ℂ) (ε : ι → 𝓀[k]ˣ) (i : ι) (l : List ι) :
    a.sAll q χ ε (i :: l) = sOp (a.α i) (a.P i) q (χ i) (ε i) ∘ a.sAll q χ ε l := rfl

theorem place (a : PairDat p A S n) (hinj : Function.Injective fun i => (p i).v) (q : Unif k)
    (χ : AddChar k Circle) (hχ : HasConductor χ 1) (ε : 𝓀[k]ˣ) (i : ι) :
    (∃ c c' : GA D A →₀ ℂ, (∀ g, c g ≠ 0 → g ∈ grpAt A (· = (p i).v)) ∧ (∀ g, c' g ≠ 0 → g ∈ grpAt A (· = (p i).v)) ∧
      (∀ φ, sOp (a.α i) (a.P i) q (resChar χ hχ q) ε φ = act c φ) ∧
      ∀ φ, a.Ram φ → a.Ram (act c' φ) ∧ sOp (a.α i) (a.P i) q (resChar χ hχ q) ε (act c' φ) = φ) ∧
    Set.MapsTo (sOp (a.α i) (a.P i) q (resChar χ hχ q) ε) {φ | a.Ram φ} {φ | a.Ram φ} ∧
    Set.InjOn (sOp (a.α i) (a.P i) q (resChar χ hχ q) ε) {φ | a.Ram φ} := by
  obtain ⟨hbij, -, c, c', hc, hc'⟩ := GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k (p i) n q χ hχ _ rfl ε A (a.α i) (a.P i)
  have hC := mapDomain_mem _ (gl_mem (a.α i)) c
  have hC' := mapDomain_mem _ (gl_mem (a.α i)) c'
  have hT : ∀ φ, sOp (a.α i) (a.P i) q (resChar χ hχ q) ε φ = act (Finsupp.mapDomain (a.α i).gl c) φ :=
    fun φ => (hc φ).trans (sum_rep_eq _ _ _)
  have other : ∀ C₀ : GA D A →₀ ℂ, (∀ g, C₀ g ≠ 0 → g ∈ grpAt A (· = (p i).v)) → ∀ j, j ≠ i → ∀ φ,
      RamAt (a.α j) (a.P j) φ → RamAt (a.α j) (a.P j) (act C₀ φ) := fun C₀ hC₀ j hj φ hφ =>
    ramAt_act _ _ C₀ (fun x hx g => grpAt_comm A (fun e => hj (hinj e)) (hC₀ x hx) (gl_mem _ g)) hφ
  refine ⟨⟨_, _, hC, hC', hT, fun φ hφ => ?_⟩, fun φ hφ => ⟨?_, fun j => ?_⟩, hbij.injOn.mono fun φ hφ => hφ.2 i⟩
  · obtain ⟨h1, h2⟩ := hc' φ (hφ.2 i)
    rw [sum_rep_eq] at h1 h2
    refine ⟨⟨isContAut_act _ hφ.1, fun j => ?_⟩, h1⟩
    rcases eq_or_ne j i with rfl | hj
    · exact h2
    · exact other _ hC' j hj φ (hφ.2 j)
  · rw [hT]; exact isContAut_act _ hφ.1
  · rcases eq_or_ne j i with rfl | hj
    · exact hbij.mapsTo (hφ.2 j)
    · rw [hT]; exact other _ hC j hj φ (hφ.2 j)

end GlobalTheory.FinPl.AllBij

namespace GlobalTheory.FinPl

open AllBij in

theorem allBijective_all : ∀ D : D7, AllBijective D := by
  intro D k _ _ _ _ ι p q χ hχ ε n _ _ A S a hinj I
  have hsub : ∀ i, grpAt A (· = (p i).v) ≤ grpAt A fun v => ∃ i, v = (p i).v :=
    fun i => congGrp_mono A (idAt_mono fun v hv => ⟨i, hv⟩)
  have key : ∀ I : List ι, Set.MapsTo (a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I) {φ | a.Ram φ} {φ | a.Ram φ} ∧
      Set.InjOn (a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I) {φ | a.Ram φ} ∧
      ∃ c c' : GA D A →₀ ℂ, (∀ g, c g ≠ 0 → g ∈ grpAt A fun v => ∃ i, v = (p i).v) ∧
        (∀ g, c' g ≠ 0 → g ∈ grpAt A fun v => ∃ i, v = (p i).v) ∧
        (∀ φ, a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I φ = act c φ) ∧
        ∀ φ, a.Ram φ → a.Ram (act c' φ) ∧ a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I (act c' φ) = φ := by
    intro I
    induction I with
    | nil =>
      have h1 : ∀ g, (Finsupp.single (1 : GA D A) (1 : ℂ)) g ≠ 0 → g ∈ grpAt A fun v => ∃ i, v = (p i).v :=
        fun g h => by rw [(Finsupp.single_apply_ne_zero.1 h).1]; exact Subgroup.one_mem _
      refine ⟨fun φ h => h, fun φ _ ψ _ h => h, _, _, h1, h1, fun φ => (act_single_one φ).symm, fun φ h => ?_⟩
      rw [act_single_one]; exact ⟨h, rfl⟩
    | cons i l ih =>
      obtain ⟨⟨C, C', hC, hC', hT, hinv⟩, maps, inj⟩ := place a hinj q (χ i) (hχ i) (ε i) i
      obtain ⟨mapsl, injl, c, c', hc, hc', hl, hinvl⟩ := ih
      rw [sAll_cons]
      refine ⟨maps.comp mapsl, inj.comp injl mapsl, cmul C c, cmul c' C', cmul_mem (fun g h => hsub i (hC g h)) hc,
        cmul_mem hc' (fun g h => hsub i (hC' g h)), fun φ => ?_, fun φ hφ => ?_⟩
      · rw [act_cmul, ← hl, Function.comp_apply, hT]
      · rw [act_cmul]
        obtain ⟨h1, h2⟩ := hinv φ hφ
        obtain ⟨h3, h4⟩ := hinvl _ h1
        refine ⟨h3, ?_⟩
        rw [Function.comp_apply, h4, h2]
  obtain ⟨maps, inj, c, c', hc, hc', hT, hinv⟩ := key I
  exact ⟨⟨maps, inj, fun φ hφ => ⟨act c' φ, (hinv φ hφ).1, (hinv φ hφ).2⟩⟩, c, c',
    fun g h => h.elim (hc g) (hc' g), hT, hinv⟩

end GlobalTheory.FinPl
