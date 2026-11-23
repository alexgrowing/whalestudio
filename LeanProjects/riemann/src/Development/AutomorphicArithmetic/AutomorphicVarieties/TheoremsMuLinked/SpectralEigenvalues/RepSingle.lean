import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.TracePartialCharpolySingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.TrPoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem tr_map {R S G : Type} [CommRing R] [CommRing S] [Group G] {n : ℕ} (D : GDet n R G)
    (f : R →+* S) (z : MonoidAlgebra R G) :
    (D.map f).tr (MonoidAlgebra.mapRingHom G f z) = f (D.tr z) :=
  ((UpperTheory.V.CA.d_gmap D).2.2.1 f z).2 1

private theorem tr_rep {R G : Type} [CommRing R] [Group G] {n : ℕ} (hn : 1 ≤ n) (ρ : G →* Matrix (Fin n) (Fin n) R)
    (z : MonoidAlgebra R G) : (GDet.ofRep ρ).tr z = (GDet.repAlg ρ R z).trace := by
  have h : (GDet.ofRep ρ).chi z = (GDet.repAlg ρ R z).charpoly := by
    change (GDet.repAlg ρ (Polynomial R) _).det = Matrix.det _
    congr 1
    rw [map_sub, Matrix.charmatrix]
    congr 1
    · ext i j : 2
      simp [GDet.repAlg, Matrix.one_apply, Matrix.diagonal_apply]
    · induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | single g r => ext i j : 2; simp [GDet.repAlg]
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [GDet.tr, GDet.lam, h, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
  simp

private theorem rep_single {R G : Type} [CommRing R] [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) R) (g : G) (a : R) :
    GDet.repAlg ρ R (MonoidAlgebra.single g a) = a • ρ g := by
  ext i j; simp [GDet.repAlg]

private theorem rep_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (φ : H →* G) :
    (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ) := by
  refine GDet.ext fun B _ _ x => ?_
  change (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ x)).det = (GDet.repAlg (ρ.comp φ) B x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r => simp [GDet.repAlg]

private noncomputable def qq {R G : Type} [CommRing R] [Group G] {n : ℕ} (E : ℕ) (ph : G) (u : Fin n → R) (i : Fin n) :
    MonoidAlgebra R G :=
  (List.ofFn fun k => if k = i then 1 else MonoidAlgebra.single ph (1 : R) - MonoidAlgebra.single 1 (u k)).prod ^ (E + 1)

private theorem qq_map {R S G : Type} [CommRing R] [CommRing S] [Group G] {n : ℕ} (f : R →+* S) (E : ℕ) (ph : G)
    (u : Fin n → R) (i : Fin n) :
    MonoidAlgebra.mapRingHom G f (qq E ph u i) = qq E ph (fun k => f (u k)) i := by
  simp [qq, map_list_prod, List.map_ofFn, Function.comp_def, apply_ite (MonoidAlgebra.mapRingHom G f)]

private theorem qq_tr {O G : Type} [CommRing O] [IsDomain O] [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) O) (E : ℕ) (ph : G)
    (α : Fin n → O) (i : Fin n) (h : (ρ ph).charpoly = ∏ k, (Polynomial.X - Polynomial.C (α k))) :
    (GDet.ofRep ρ).tr (qq E ph α i) = (∏ k ∈ Finset.univ.erase i, (α i - α k)) ^ (E + 1) := by
  have e : GDet.repAlg ρ O (qq E ph α i) = Polynomial.aeval (ρ ph)
      ((∏ k, if k = i then 1 else (Polynomial.X - Polynomial.C (α k))) ^ (E + 1)) := by
    rw [qq, map_pow, map_pow, ← List.prod_ofFn, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 3
    funext k
    by_cases hk : k = i <;> simp [hk, rep_single, Algebra.algebraMap_eq_smul_one]
  rw [tr_rep (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) i.2)), e, Sp.trp O n _ α _ h,
    Finset.sum_eq_single i]
  · rw [Polynomial.eval_pow, Polynomial.eval_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), if_pos rfl,
      Polynomial.eval_one, mul_one]
    congr 1
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [if_neg (Finset.mem_erase.1 hk).1]
    simp
  · intro a _ ha
    rw [Polynomial.eval_pow, Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha]), zero_pow E.succ_ne_zero]
  · exact fun h => (h (Finset.mem_univ _)).elim

private theorem core {O R T G X : Type} [CommRing O] [IsDomain O] [CommRing R] [CommRing T] [Algebra O R] [Algebra O T] [Group G]
    [AddCommGroup X] [Module O X] {n : ℕ} (D : GDet n R G) (c : R →+* T) (hc : ∀ a, c (algebraMap O R a) = algebraMap O T a)
    (x : T →ₐ[O] O) (del : T →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (hD : D.map ((x : T →+* O).comp c) = GDet.ofRep ρ)
    (ph ta : G) (α : Fin n → O) (E : ℕ) (i : Fin n) (u : Fin n → T) (y : T) (hn : 1 ≤ n) (hta : ρ ta = 1)
    (h : (ρ ph).charpoly = ∏ k, (Polynomial.X - Polynomial.C (α k))) (hu : ∀ k, x (u k) = α k) (hy : x y = 0)
    (hd : IsDer x del) :
    x ((D.map c).tr (twoPowerModulus E ph ta u i y)) = 0 ∧ del ((D.map c).tr (twoPowerModulus E ph ta u i y)) =
      del (c (D.tr (twoPowerModulus E ph ta (fun k => algebraMap O R (α k)) i 0))) -
        (∏ k ∈ Finset.univ.erase i, (α i - α k)) ^ (E + 1) • del y := by
  have hx : ∀ z, x ((D.map c).tr z) = (GDet.ofRep ρ).tr (MonoidAlgebra.mapRingHom G (x : T →+* O) z) := fun z => by
    rw [← hD, ← (UpperTheory.V.CA.d_gmap D).2.1 c (x : T →+* O), tr_map]
    rfl
  obtain ⟨k1, k2⟩ := Sp.q2 O T G X n (D.map c) x del ta y (qq E ph u i) hn hd hy fun g => by
    rw [hx, hx, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single, tr_rep hn, tr_rep hn, rep_single, rep_single,
      map_mul, hta, mul_one]
  refine ⟨k1, k2.trans ?_⟩
  have e1 : (fun k => (x : T →+* O) (u k)) = α := funext hu
  have e2 : MonoidAlgebra.mapRingHom G c (twoPowerModulus E ph ta (fun k => algebraMap O R (α k)) i 0) =
      MonoidAlgebra.mapRingHom G ((algebraMap O T).comp (x : T →+* O)) (qq E ph u i) *
        (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 0) := by
    change MonoidAlgebra.mapRingHom G c (qq E ph _ i * _) = _
    rw [map_mul, qq_map, qq_map]
    congr 1
    · congr 1
      funext k
      rw [hc, ← hu k]
      rfl
    · simp
  rw [← e2, tr_map, hx, qq_map, e1, qq_tr ρ E ph α i h]

theorem UpperTheory.V.Th.Sp.q2op :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N) (y : Pt G0.frame O n) (x : B →ₐ[O] O) (ph ta : G.G₀) (α : Fin n → O) (E : ℕ) (j : Fin q) (i : Fin n) (xT : PUY A.R q n →ₐ[O] O) (X : Type) [AddCommGroup X] [Module O X] (del : PUY A.R q n →ₗ[O] X), 1 ≤ n → u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ → h.p₀ ta = 1 → (mat y.ρ (h.p₀ ph)).charpoly = ∏ k, (Polynomial.X - Polynomial.C (α k)) → (∀ s, xT (MvPolynomial.C s) = x (A.β s)) → (∀ k, xT (uV A.R j k) = α k) → xT (yV A.R j i) = 0 → IsDer xT del → xT ((A.p.D.map (MvPolynomial.C : A.R →+* PUY A.R q n)).tr (twoPowerModulus E ph ta (uV A.R j) i (yV A.R j i))) = 0 ∧ del ((A.p.D.map (MvPolynomial.C : A.R →+* PUY A.R q n)).tr (twoPowerModulus E ph ta (uV A.R j) i (yV A.R j i))) = del (MvPolynomial.C (A.p.D.tr (twoPowerModulus E ph ta (fun k => algebraMap O A.R (α k)) i 0))) - (∏ k ∈ Finset.univ.erase i, (α i - α k)) ^ (E + 1) • del (yV A.R j i) := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A y x ph ta α E j i xT X _ _ del hn hmap hta hα hC hu hy hd
  refine core (O := O) (T := PUY A.R q n) A.p.D MvPolynomial.C (fun a => rfl) xT del ((mat y.ρ).comp h.p₀) ?_ ph ta α E i _ _ hn ?_ hα hu hy hd
  · have e : (xT : PUY A.R q n →+* O).comp MvPolynomial.C = x.toRingHom.comp A.β.toRingHom := RingHom.ext hC
    rw [e, ← (UpperTheory.V.CA.d_gmap A.p.D).2.1, A.β_pair.1, ← rep_comap, ← hmap.1]
    rfl
  · rw [MonoidHom.comp_apply, hta, map_one]
