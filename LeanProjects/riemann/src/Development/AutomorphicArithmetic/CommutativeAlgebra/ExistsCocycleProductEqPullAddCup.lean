import Development.AutomorphicArithmetic.CommutativeAlgebra.MapZeroS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAWStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Kun

theorem UpperTheory.exists_cocycle_product_eq_pull_add_cup :
    ∀ (R : Type) [CommRing R] (W X : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I)
        (κ : Cocycle ((chains R).obj (sch.obj W)) P 1) {m n : ℤ} (h : m + 1 = n)
        (α₁ : Cocycle ((chains R).obj (sch.obj X)) I n) (α₂ : Cocycle ((chains R).obj (sch.obj X)) Q m),
        ∃ β : Cocycle ((chains R).obj (sch.obj (W ⨯ X))) I n,
          CohomologyClass.mk β =
              cpull ((chains R).map (sch.map (prod.snd : W ⨯ X ⟶ X))) I n (CohomologyClass.mk α₁) +
                μ.cup (sch.obj (W ⨯ X)) h
                  (cpull ((chains R).map (sch.map (prod.snd : W ⨯ X ⟶ X))) Q m (CohomologyClass.mk α₂))
                  (cpull ((chains R).map (sch.map (prod.fst : W ⨯ X ⟶ W))) P 1 (CohomologyClass.mk κ)) ∧
            sg β = Sec.res (prod.snd : W ⨯ X ⟶ X) (sg α₁) +
              μ.mul (W ⨯ X) m 1 n h (Sec.res (prod.snd : W ⨯ X ⟶ X) (sg α₂))
                (Sec.res (prod.fst : W ⨯ X ⟶ W) (sg κ)) := by
  intro R _ W X I Q P μ κ m n h α₁ α₂
  let A := zcomp (Cocycle.ofHom ((chains R).map (sch.map (prod.snd : W ⨯ X ⟶ X)))) α₂ (zero_add m)
  let B := zcomp (Cocycle.ofHom ((chains R).map (sch.map (prod.fst : W ⨯ X ⟶ W)))) κ (zero_add 1)
  let C := zcomp (Cocycle.ofHom ((chains R).map (sch.map (prod.snd : W ⨯ X ⟶ X)))) α₁ (zero_add n)
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ h).1 A B
  have hc := (GlobalTheory.T.cup_eq_class_of_isAW R μ h).2 A B γ hγ
  refine ⟨C + γ, ?_, ?_⟩
  · rw [CohomologyClass.mk_add, ← hc]
    rfl
  · have hadd : sg (C + γ) = sg C + sg γ :=
      ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj (W ⨯ X)) (I := I) (n := n)).1 C.1 γ.1 0 n (by simp) (W ⨯ X) (𝟙 _)).1
    have hC : sg C = Sec.res (prod.snd : W ⨯ X ⟶ X) (sg α₁) := sg_pull _ α₁
    have hA : sg A = Sec.res (prod.snd : W ⨯ X ⟶ X) (sg α₂) := sg_pull _ α₂
    have hB : sg B = Sec.res (prod.fst : W ⨯ X ⟶ W) (sg κ) := sg_pull _ κ
    have key : ∀ (d e : ℤ) (hd : -((0 : ℕ) : ℤ) + m = d) (he : -((0 : ℕ) : ℤ) + 1 = e) (hw : d + e = n),
        μ.mul (W ⨯ X) d e n hw (ev A.1 0 d hd (W ⨯ X) (𝟙 _)) (ev B.1 0 e he (W ⨯ X) (𝟙 _)) =
          μ.mul (W ⨯ X) m 1 n h (sg A) (sg B) := by
      intro d e hd he hw
      obtain rfl : m = d := by simpa using hd
      obtain rfl : (1 : ℤ) = e := by simpa using he
      rfl
    have hg : sg γ = μ.mul (W ⨯ X) m 1 n h (sg A) (sg B) := by
      have h0 := hγ 0 n (by simp) (W ⨯ X) (𝟙 _)
      rw [Fin.sum_univ_one] at h0
      refine h0.trans ?_
      have e : ((1 : ℤ) * (((0 : Fin 1) : ℕ) : ℤ)).negOnePow = 1 := by simp
      rw [e, one_smul]
      exact key _ _ rfl rfl _
    rw [hadd, hC, hg, hA, hB]
