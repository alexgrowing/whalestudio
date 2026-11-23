import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam.LevAlg

variable {S : Scheme.{0}}

section Hom

variable {G H : Over S} [GrpObj G] [GrpObj H]

theorem isMonHom_of_mulComp (f : G ⟶ H)
    (h : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f where
  one_hom := by
    rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact map_one (MonoidHom.mk' (fun x : 𝟙_ (Over S) ⟶ G ↦ x ≫ f) (h _))
  mul_hom := by
    rw [MonObj.mul_eq_mul, h, MonObj.mul_eq_mul, MonObj.comp_mul]
    simp

theorem isMonHom_mul [IsCommMonObj H] (f g : G ⟶ H) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) :=
  isMonHom_of_mulComp _ fun T x y ↦ by
    simp only [MonObj.comp_mul, MonObj.mul_comp]
    exact mul_mul_mul_comm _ _ _ _

theorem isMonHom_one : IsMonHom (1 : G ⟶ H) :=
  isMonHom_of_mulComp _ fun T x y ↦ by simp

theorem isMonHom_zpow [IsCommMonObj H] (f : G ⟶ H) [IsMonHom f] (n : ℤ) : IsMonHom (f ^ n) :=
  isMonHom_of_mulComp _ fun T x y ↦ by
    simp only [GrpObj.comp_zpow, MonObj.mul_comp, mul_zpow]

theorem isMonHom_prod [IsCommMonObj H] {K : Type} (s : Finset K) (f : K → (G ⟶ H))
    (hf : ∀ i, IsMonHom (f i)) : IsMonHom (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isMonHom_one : IsMonHom (1 : G ⟶ H))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    haveI := hf a
    exact isMonHom_mul _ _

end Hom

section Obj

variable (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem mkZ_pa {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  unfold mkZ pa
  rw [lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk T u) ⟨i⟩

theorem mkZ_pb {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  unfold mkZ pb
  rw [lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk T v) ⟨j⟩

theorem zob_ext {T : Over S} (f g : T ⟶ Zob A B) (ha : ∀ i, f ≫ pa A B i = g ≫ pa A B i)
    (hb : ∀ j, f ≫ pb A B j = g ≫ pb A B j) : f = g := by
  apply CartesianMonoidalCategory.hom_ext
  · apply (Out.powIsLimit A 4).hom_ext
    rintro ⟨i⟩
    simpa [pa] using ha i
  · apply (Out.powIsLimit B 4).hom_ext
    rintro ⟨j⟩
    simpa [pb] using hb j

instance isMonHom_pa (i : Fin 4) : IsMonHom (pa A B i) := by
  unfold pa; infer_instance

instance isMonHom_pb (j : Fin 4) : IsMonHom (pb A B j) := by
  unfold pb; infer_instance

theorem isMonHom_mkZ {T : Over S} [GrpObj T] (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B))
    (hu : ∀ i, IsMonHom (u i)) (hv : ∀ j, IsMonHom (v j)) : IsMonHom (mkZ A B u v) :=
  isMonHom_of_mulComp _ fun T' x y ↦ by
    apply zob_ext
    · intro i
      haveI := hu i
      simp only [Category.assoc, mkZ_pa, MonObj.mul_comp]
    · intro j
      haveI := hv j
      simp only [Category.assoc, mkZ_pb, MonObj.mul_comp]

theorem isMonHom_incZ : IsMonHom (incZ A B) := by
  unfold incZ
  apply isMonHom_mkZ
  · intro i
    split_ifs
    · infer_instance
    · exact isMonHom_one
  · intro j
    exact isMonHom_one

theorem isMonHom_actZ (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) [IsMonHom la] [IsMonHom mu] (N : ord d) :
    IsMonHom (actZ A B d la mu N) := by
  unfold actZ
  apply isMonHom_mkZ
  · intro i
    apply isMonHom_prod
    intro j
    haveI := isMonHom_zpow (pa A B j) ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inl j) (Sum.inl i))
    haveI := isMonHom_zpow (pb A B j ≫ mu)
      ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inr j) (Sum.inl i) / (d : ℤ))
    exact isMonHom_mul _ _
  · intro i
    apply isMonHom_prod
    intro j
    haveI := isMonHom_zpow (pa A B j ≫ la) ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inl j) (Sum.inr i))
    haveI := isMonHom_zpow (pb A B j) ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inr j) (Sum.inr i))
    exact isMonHom_mul _ _

end Obj

end GlobalTheory.ZarhinFam.LevAlg

namespace GlobalTheory.ZarhinFam.LevAlg

theorem levZ_add_tors : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → (∀ a b, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (a + b) = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a * (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) b) ∧ ∀ a, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a ^ M = 1 := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ _ _ _ _ κ _
  haveI : IsMonHom la := hZ.2.2.2.1
  haveI : IsMonHom mu := hZ.2.2.2.2.1
  have hg : ∀ k, IsMonHom (incZ c.A B ≫ actZ c.A B d la mu (oMat d k)) := fun k => by
    haveI := isMonHom_incZ c.A B
    haveI := isMonHom_actZ c.A B d la mu (oMat d k)
    infer_instance
  constructor
  · intro a b
    simp only [levZ, List.prod_ofFn]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    haveI := hg k
    rw [map_add, c.lev_add, MonObj.mul_comp]
  · intro a
    simp only [levZ, List.prod_ofFn]
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun k _ => ?_
    haveI := hg k
    rw [← MonObj.pow_comp, c.lev_tors]
    simp

end GlobalTheory.ZarhinFam.LevAlg
