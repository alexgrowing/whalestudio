import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam.RelAlg

open GlobalTheory.ZarhinFam

section Obj

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem mkZ_pa {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  simp only [mkZ, pa]
  rw [lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk T u) ⟨i⟩

theorem mkZ_pb {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  simp only [mkZ, pb]
  rw [lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk T v) ⟨j⟩

theorem zob_ext {T : Over S} {f g : T ⟶ Zob A B} (ha : ∀ i, f ≫ pa A B i = g ≫ pa A B i)
    (hb : ∀ j, f ≫ pb A B j = g ≫ pb A B j) : f = g := by
  apply CartesianMonoidalCategory.hom_ext
  · apply (Out.powIsLimit A 4).hom_ext
    rintro ⟨i⟩
    simpa [pa] using ha i
  · apply (Out.powIsLimit B 4).hom_ext
    rintro ⟨j⟩
    simpa [pb] using hb j

instance isMonHom_pa (i : Fin 4) : IsMonHom (pa A B i) := by
  unfold pa
  infer_instance

instance isMonHom_pb (j : Fin 4) : IsMonHom (pb A B j) := by
  unfold pb
  infer_instance

theorem isMonHom_of_coords {X : Over S} [MonObj X] (f : X ⟶ Zob A B)
    (ha : ∀ i, IsMonHom (f ≫ pa A B i)) (hb : ∀ j, IsMonHom (f ≫ pb A B j)) : IsMonHom f where
  one_hom := zob_ext A B (fun i => by
      haveI := ha i
      rw [Category.assoc, IsMonHom.one_hom (f := f ≫ pa A B i), IsMonHom.one_hom (f := pa A B i)])
    (fun j => by
      haveI := hb j
      rw [Category.assoc, IsMonHom.one_hom (f := f ≫ pb A B j), IsMonHom.one_hom (f := pb A B j)])
  mul_hom := zob_ext A B (fun i => by
      haveI := ha i
      rw [Category.assoc, IsMonHom.mul_hom (f := f ≫ pa A B i), Category.assoc,
        IsMonHom.mul_hom (f := pa A B i), ← Category.assoc, tensorHom_comp_tensorHom])
    (fun j => by
      haveI := hb j
      rw [Category.assoc, IsMonHom.mul_hom (f := f ≫ pb A B j), Category.assoc,
        IsMonHom.mul_hom (f := pb A B j), ← Category.assoc, tensorHom_comp_tensorHom])

theorem isMonHom_incZ : IsMonHom (incZ A B) := by
  apply isMonHom_of_coords
  · intro i
    rw [incZ, mkZ_pa]
    split_ifs
    · infer_instance
    · exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
  · intro j
    rw [incZ, mkZ_pb]
    exact inferInstanceAs (IsMonHom (toUnit A ≫ η[B]))

theorem isMonHom_prZ : IsMonHom (prZ A B) := by
  unfold prZ pa
  infer_instance

theorem incZ_prZ : incZ A B ≫ prZ A B = 𝟙 A := by
  rw [incZ, prZ, mkZ_pa]
  simp

theorem prZ_incZ (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) : prZ A B ≫ incZ A B = actZ A B d la mu (idem d) := by
  apply zob_ext
  · intro i
    rw [Category.assoc, incZ, mkZ_pa, actZ, mkZ_pa]
    fin_cases i <;> simp [prZ, idem, Matrix.single_apply, Fin.prod_univ_four, MonObj.comp_one]
  · intro j
    rw [Category.assoc, incZ, mkZ_pb, actZ, mkZ_pb]
    fin_cases j <;> simp [prZ, idem, Matrix.single_apply, Fin.prod_univ_four, MonObj.comp_one]

end Obj

end GlobalTheory.ZarhinFam.RelAlg

noncomputable section

namespace GlobalTheory.ZarhinFam.RelAlg

open GlobalTheory.ZarhinFam

section Lev

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

def precompHom {X Y M : Over S} [GrpObj M] [IsCommMonObj M] (x : X ⟶ Y) : (Y ⟶ M) →* (X ⟶ M) where
  toFun g := x ≫ g
  map_one' := MonObj.comp_one x
  map_mul' g₁ g₂ := MonObj.comp_mul x g₁ g₂

theorem one_comp_actZ (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) [IsMonHom la] [IsMonHom mu] (N : ord d) :
    (1 : 𝟙_ (Over S) ⟶ Zob A B) ≫ actZ A B d la mu N = 1 := by
  apply zob_ext
  · intro i
    rw [Category.assoc, actZ, mkZ_pa, MonObj.one_comp (pa A B i)]
    change precompHom (1 : 𝟙_ (Over S) ⟶ Zob A B) _ = 1
    rw [map_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [map_mul, map_zpow, map_zpow]
    change (1 ≫ pa A B j) ^ _ * (1 ≫ pb A B j ≫ mu) ^ _ = 1
    rw [MonObj.one_comp, ← Category.assoc, MonObj.one_comp, MonObj.one_comp]
    simp
  · intro j
    rw [Category.assoc, actZ, mkZ_pb, MonObj.one_comp (pb A B j)]
    change precompHom (1 : 𝟙_ (Over S) ⟶ Zob A B) _ = 1
    rw [map_prod]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [map_mul, map_zpow, map_zpow]
    change (1 ≫ pa A B k ≫ la) ^ _ * (1 ≫ pb A B k) ^ _ = 1
    rw [MonObj.one_comp (pa A B k ≫ la), MonObj.one_comp (pb A B k)]
    simp

theorem oMat_zero (d : ℕ) : oMat d 0 = idem d := rfl

end Lev

end GlobalTheory.ZarhinFam.RelAlg

namespace GlobalTheory.ZarhinFam

open GlobalTheory.ZarhinFam.RelAlg

theorem zRel_alg : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → IsMonHom (GlobalTheory.ZarhinFam.incZ c.A B) ∧ IsMonHom (GlobalTheory.ZarhinFam.prZ c.A B) ∧ GlobalTheory.ZarhinFam.incZ c.A B ≫ GlobalTheory.ZarhinFam.prZ c.A B = 𝟙 c.A ∧ GlobalTheory.ZarhinFam.prZ c.A B ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.idem d) ∧ ∀ a, c.lev a ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (GlobalTheory.ZarhinFam.jlMap h a) := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ _ _ _ _ κ hκ
  haveI : IsMonHom la := hZ.2.2.2.1
  haveI : IsMonHom mu := hZ.2.2.2.2.1
  haveI := isMonHom_incZ c.A B
  have hpi := prZ_incZ c.A B d la mu
  refine ⟨isMonHom_incZ c.A B, isMonHom_prZ c.A B, incZ_prZ c.A B, hpi, fun a => ?_⟩
  have hlev0 : c.lev 0 = 1 := by
    have h0 := c.lev_add 0 0
    rw [add_zero] at h0
    exact left_eq_mul.mp h0
  rw [levZ, List.prod_ofFn, Fintype.prod_eq_single 0 (fun k hk => by
    rw [hκ.2.2 k hk a, hlev0, ← Category.assoc, MonObj.one_comp, one_comp_actZ])]
  rw [hκ.2.1 a, oMat_zero, ← hpi, ← Category.assoc (incZ c.A B), incZ_prZ, Category.id_comp]

end GlobalTheory.ZarhinFam
