import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompatStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolDict.PrincLev

def congGroup {D : D7} (V : HSp D) (N : ℕ) : Subgroup (GA D V) where
  carrier := {k | GlobalTheory.Member.FinCong V N k}
  one_mem' := GlobalTheory.Member.PrincLevel.finCong_one V N
  mul_mem' := fun ha hb => GlobalTheory.Member.PrincLevel.finCong_mul ha hb
  inv_mem' := fun ha => GlobalTheory.Member.PrincLevel.finCong_inv ha

theorem isOpen_congGroup {D : D7} (V : HSp D) {N : ℕ} (hN : 0 < N) : IsOpen (congGroup V N : Set (GA D V)) :=
  haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  Subgroup.isOpen_of_mem_nhds _ (GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN)

theorem mem_of_isLevelK {D : D7} {V W : HSp D} (hV : V = W) {N : ℕ} {Kf : Subgroup (GA D V)} (hK : IsLevelK V N Kf)
    (k : GA D W) (h1 : k ∈ congGroup W N) (h2 : k ∈ GfC W) : cast (congrArg (GA D) hV.symm) k ∈ Kf := by
  subst hV
  exact (hK k).2 ⟨h2, h1⟩

theorem mem_levG_triv_iff {D : D7} {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    k ∈ levG (Wc D i) (L.βW i) (L.datWp i L.triv) ↔ IsLevelLift (Wc D i) (L.βW i) (L.datWp i L.triv) 1 k :=
  ⟨fun h => ⟨h.1, h.2.1, Subgroup.mem_bot.1 h.2.2⟩, fun h => ⟨h.1, h.2.1, Subgroup.mem_bot.2 h.2.2⟩⟩

theorem levChi_triv_eq_one {D : D7} {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  have h : ∀ x, ext1 L.triv.H L.triv.chi x = 1 := fun x => by
    unfold ext1; split_ifs <;> rfl
  unfold levChi levFn
  simp [LevCh.datWp, datY]
  exact h _

set_option maxHeartbeats 1000000 in

theorem principal_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, (∀ g : GA D (Wc D i), g ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) ↔ cast (congrArg (GA D) hV.symm) g ∈ T.Kf ((i : ℕ) + 1) (res T σ)) ∧ (∀ k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)), levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1) ∧ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) ≤ GfC (Wc D i) ∧ ∃ U : Subgroup (GA D (Wc D i)), IsOpen (U : Set (GA D (Wc D i))) ∧ ∀ k ∈ U, k ∈ GfC (Wc D i) → k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL _ ht hpb i σ hσ hV
  have key : ∀ g : GA D (Wc D i), g ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv) ↔
      cast (congrArg (GA D) hV.symm) g ∈ T.Kf ((i : ℕ) + 1) (res T σ) := fun g =>
    (mem_levG_triv_iff R.toLevCh i g).trans (GlobalTheory.T.level_character_embedding_compat T R κ v₀ hL ht hpb i (res T σ) hσ hV g)
  have hg : 0 < D.host.g 0 * D.host.g 1 := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  refine ⟨key, fun k _ => levChi_triv_eq_one R.toLevCh i k, fun k hk => hk.1,
    congGroup (Wc D i) (D.host.g 0 * D.host.g 1), isOpen_congGroup _ hg, fun k h1 h2 => (key k).2 ?_⟩
  exact mem_of_isLevelK hV (ht.laws.levelK _ (inR i) _ hσ) k h1 h2

end GlobalTheory.HolDict.PrincLev
