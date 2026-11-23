import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.InOfIntIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.SpanOGen

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem liftMx {A K : Type} [CommRing A] [CommRing K] {n : ℕ} (f : A →+* K) (Z : Matrix (Fin n) (Fin n) K)
    (h : ∀ i j, ∃ a, f a = Z i j) : ∃ Z₀ : Matrix (Fin n) (Fin n) A, f.mapMatrix Z₀ = Z := by
  choose k hk using h
  refine ⟨Matrix.of fun i j => k i j, ?_⟩
  ext i j
  simp [RingHom.mapMatrix_apply, hk]

private theorem injM {A K : Type} [CommRing A] [CommRing K] {n : ℕ} (f : A →+* K) (hf : Function.Injective f) :
    Function.Injective (f.mapMatrix : Matrix (Fin n) (Fin n) A → Matrix (Fin n) (Fin n) K) := by
  intro X X' hX
  ext i j
  apply hf
  have := congrFun (congrFun hX i) j
  simpa [RingHom.mapMatrix_apply] using this

private theorem liftU {A K : Type} [Monoid A] [Monoid K] (f : A →* K) (hf : Function.Injective f) (u : Kˣ)
    (h : ∃ a, f a = u) (h' : ∃ a, f a = (u⁻¹ : Kˣ)) : ∃ u₀ : Aˣ, Units.map f u₀ = u := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'
  refine ⟨⟨a, b, hf ?_, hf ?_⟩, ?_⟩
  · rw [map_mul, ha, hb, map_one]
    simp
  · rw [map_mul, ha, hb, map_one]
    simp
  · ext
    simp [ha]

private theorem liftG {A K : Type} [CommRing A] [CommRing K] {n : ℕ} (f : A →+* K) (hf : Function.Injective f)
    (g : GL (Fin n) K) (h : ∀ i j, ∃ a, f a = (g : Matrix (Fin n) (Fin n) K) i j)
    (h' : ∀ i j, ∃ a, f a = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) :
    ∃ g₀ : GL (Fin n) A, GeneralLinearGroup.map f g₀ = g := by
  obtain ⟨a, ha⟩ := liftMx f _ h
  obtain ⟨b, hb⟩ := liftMx f _ h'
  obtain ⟨u, hu⟩ := liftU f.mapMatrix.toMonoidHom (injM f hf) g ⟨a, ha⟩ ⟨b, hb⟩
  refine ⟨u, Units.ext ?_⟩
  exact congrArg Units.val hu

private theorem liftH {H A B : Type} [Group H] [Group A] [Group B] (j : A →* B) (hj : Function.Injective j) (ρ : H →* B)
    (h : ∀ g, ∃ a, j a = ρ g) : ∃ ρ₀ : H →* A, j.comp ρ₀ = ρ := by
  choose k hk using h
  refine ⟨MonoidHom.mk' k (fun a b => hj (by rw [hk, map_mul, map_mul, hk, hk])), ?_⟩
  ext g
  show j (k g) = ρ g
  exact hk g

private theorem coeG {A K : Type} [CommRing A] [CommRing K] {n : ℕ} (f : A →+* K) (g : GL (Fin n) A) :
    ((GeneralLinearGroup.map f g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = f.mapMatrix (g : Matrix (Fin n) (Fin n) A) := rfl

private theorem injG {A K : Type} [CommRing A] [CommRing K] {n : ℕ} (f : A →+* K) (hf : Function.Injective f) :
    Function.Injective (GeneralLinearGroup.map f : GL (Fin n) A → GL (Fin n) K) := by
  intro a b hab
  apply Units.ext
  apply injM f hf
  rw [← coeG, ← coeG, hab]

private theorem mapT {A K : Type} [CommRing A] [CommRing K] {n : ℕ} (f : A →+* K) (Z : Matrix (Fin n) (Fin n) A) :
    f.mapMatrix Zᵀ = (f.mapMatrix Z)ᵀ := rfl

private theorem mapS {A K : Type} [CommRing A] [CommRing K] {n : ℕ} (f : A →+* K) (a : A) (Z : Matrix (Fin n) (Fin n) A) :
    f.mapMatrix (a • Z) = f a • f.mapMatrix Z := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.smul_apply]

private theorem epsEq {l : ℕ} [Fact l.Prime] (F : GFrame l) (c₀ c : Coef l) (g : F.G₀) :
    F.eps c₀.O (Qbar l) g = Units.map (algebraMap c.O (Qbar l) : c.O →* Qbar l) (F.eps c.O c.O g) := by
  ext
  simp [GFrame.eps, pushCh]

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Th.Nm.mkPt :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c₀ c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ) (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)) (w : F.Vl → GL (Fin n) (Qbar l)) (Y : F.Vl → Matrix (Fin n) (Fin n) (Qbar l)), Continuous ρ → Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → F.IsForm c₀.O n ρ P → ((P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -P) → (∀ u, ∀ g ∈ F.Iu u, ρ g = 1) → (∀ v, ∃ g, Function.Injective fun i => ψ v i g) → (∀ v i j, i < j → ψ v i ≠ ψ v j * (F.eps c₀.O (Qbar l)).comp (F.φ v)) → IsOrdCoc F ρ P F.Iu ψ z → (∀ v, OrdAt F ρ v (ψ v) z (w v) (Y v)) → (∀ g, InO c (mat ρ g)) → InO c (P : Matrix (Fin n) (Fin n) (Qbar l)) → InO c ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) → (∀ v, InO c (w v : Matrix (Fin n) (Fin n) (Qbar l)) ∧ InO c (((w v)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ InO c (Y v)) → (∀ g, InO c (z g)) → ∃ (y : Pt F c.O n) (z₀ : F.G₀ → Matrix (Fin n) (Fin n) c.O), IsModel y ρ P ψ ∧ (∀ g, (z₀ g).map (algebraMap c.O (Qbar l)) = z g) ∧ OCoc y z₀ := by
  intro l _ n F c₀ c ρ P ψ z w Y hρc hspan hform hsgn hine hreg hN1 hz hord hρO hPO hPiO hwO hzO
  let ι : c.O →+* Qbar l := algebraMap c.O (Qbar l)
  have hι : Function.Injective ι := Subtype.val_injective
  have lift1 : ∀ Z : Matrix (Fin n) (Fin n) (Qbar l), InO c Z → ∀ i j, ∃ a, ι a = Z i j :=
    fun Z hZ i j => ⟨⟨Z i j, hZ i j⟩, rfl⟩
  have hGL : ∀ g : GL (Fin n) (Qbar l), InO c (g : Matrix (Fin n) (Fin n) (Qbar l)) →
      InO c ((g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) →
      ∃ g₀ : GL (Fin n) c.O, GeneralLinearGroup.map ι g₀ = g :=
    fun g h1 h2 => liftG ι hι g (lift1 _ h1) (lift1 _ h2)
  have hρO' : ∀ g, InO c ((ρ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := hρO
  obtain ⟨ρ₀, hρ₀⟩ := liftH (GeneralLinearGroup.map ι) (injG ι hι) ρ
    (fun g => hGL (ρ g) (hρO' g) (by rw [← map_inv]; exact hρO' g⁻¹))
  have hρx : ∀ x, GeneralLinearGroup.map ι (ρ₀ x) = ρ x := fun x => DFunLike.congr_fun hρ₀ x
  obtain ⟨P₀, hP₀⟩ := hGL P hPO hPiO
  choose w₀ hw₀ using fun v => hGL (w v) (hwO v).1 (hwO v).2.1
  choose Y₀ hY₀ using fun v => liftMx ι (Y v) (lift1 _ (hwO v).2.2)
  choose z₀ hz₀ using fun g => liftMx ι (z g) (lift1 _ (hzO g))
  have heq : ∀ (A : Matrix (Fin n) (Fin n) c.O) (B : Matrix (Fin n) (Fin n) (Qbar l)),
      ι.mapMatrix A = B → ∀ i j, ι (A i j) = B i j := by
    intro A B hAB i j
    rw [← hAB]
    rfl
  have hz0 : ∀ (A : Matrix (Fin n) (Fin n) c.O) (B : Matrix (Fin n) (Fin n) (Qbar l)),
      ι.mapMatrix A = B → ∀ i j, B i j = 0 → A i j = 0 := by
    intro A B hAB i j hB
    apply hι
    rw [map_zero, heq A B hAB i j, hB]
  have hmρ : ∀ x, ι.mapMatrix (mat ρ₀ x) = mat ρ x := by
    intro x
    show ι.mapMatrix ((ρ₀ x : GL (Fin n) c.O) : Matrix (Fin n) (Fin n) c.O) = ((ρ x : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))
    rw [← hρx x, coeG]
  have hmP : ι.mapMatrix (P₀ : Matrix (Fin n) (Fin n) c.O) = P := by
    rw [← hP₀, coeG]
  have hmw : ∀ v, ι.mapMatrix (w₀ v : Matrix (Fin n) (Fin n) c.O) = w v := by
    intro v
    rw [← hw₀ v, coeG]
  have hmwi : ∀ v, ι.mapMatrix (((w₀ v)⁻¹ : GL (Fin n) c.O) : Matrix (Fin n) (Fin n) c.O) =
      (((w v)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    intro v
    rw [← coeG, map_inv, hw₀ v]
  have hconj : ∀ v g, GeneralLinearGroup.map ι ((w₀ v)⁻¹ * ρ₀ (F.φ v g) * w₀ v) =
      (w v)⁻¹ * ρ (F.φ v g) * w v := by
    intro v g
    rw [map_mul, map_mul, map_inv, hw₀ v, hρx]
  have hψval : ∀ v i g, ∃ a, ι a = ((ψ v i g : (Qbar l)ˣ) : Qbar l) := by
    intro v i g
    refine ⟨(((w₀ v)⁻¹ * ρ₀ (F.φ v g) * w₀ v : GL (Fin n) c.O) : Matrix (Fin n) (Fin n) c.O) i i, ?_⟩
    rw [← ((hord v g).2.1 i), ← hconj v g, coeG]
    rfl
  choose ψ₀ hψ₀ using fun v i => liftH (Units.map ι.toMonoidHom) (Units.map_injective hι) (ψ v i)
    (fun g => liftU ι.toMonoidHom hι (ψ v i g) (hψval v i g) (by rw [← map_inv]; exact hψval v i g⁻¹))
  have hψx : ∀ v i g, Units.map ι.toMonoidHom (ψ₀ v i g) = ψ v i g := fun v i g => DFunLike.congr_fun (hψ₀ v i) g
  have hmz : ∀ g, ι.mapMatrix (z₀ g) = z g := hz₀
  have hdY : ∀ v x, ι.mapMatrix (dY F (mat ρ₀) (Y₀ v) x) = dY F (mat ρ) (Y v) x := by
    intro v x
    simp only [dY, map_sub, map_mul, hmρ, hY₀]
  have hbig : ∀ v x, ι.mapMatrix ((((w₀ v)⁻¹ : GL (Fin n) c.O) : Matrix (Fin n) (Fin n) c.O) *
      (z₀ x - dY F (mat ρ₀) (Y₀ v) x) * (w₀ v : Matrix (Fin n) (Fin n) c.O)) =
      (((w v)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) *
      (z x - dY F (mat ρ) (Y v) x) * (w v : Matrix (Fin n) (Fin n) (Qbar l)) := by
    intro v x
    rw [map_mul, map_mul, map_sub, hmwi, hmz, hdY, hmw]
  have hcont : ∀ f : F.G₀ → c.O, Continuous (fun g => ι (f g)) → AdicCont (maximalIdeal c.O) f :=
    fun f hf => (inOf c).2.2.2 F.G₀ f hf
  have hcM : ∀ v g, ι.mapMatrix ((((w₀ v)⁻¹ * ρ₀ (F.φ v g) * w₀ v : GL (Fin n) c.O)) : Matrix (Fin n) (Fin n) c.O) =
      (((w v)⁻¹ * ρ (F.φ v g) * w v : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    intro v g
    rw [← coeG, hconj v g]
  refine ⟨Th.Pt.mk ρ₀ ?_ P₀ ?_ ?_ ?_ ?_ ψ₀ w₀ ?_ ?_ ?_, z₀, ⟨hρ₀, hP₀, fun v i => hψ₀ v i⟩, fun g => hz₀ g, ?_⟩
  · intro i j
    apply hcont
    have : (fun g => ι (mat ρ₀ g i j)) = fun g => mat ρ g i j := by
      funext g
      exact heq _ _ (hmρ g) i j
    rw [this]
    exact (Units.continuous_val.comp hρc).matrix_elem i j
  · rcases hsgn with h | h
    · left
      apply injM ι hι
      rw [mapT, hmP, h]
    · right
      apply injM ι hι
      rw [mapT, hmP, h, map_neg, hmP]
  · intro g
    apply injM ι hι
    rw [map_mul, map_mul, mapT, hmρ, hmρ, hmP, mapS, hmP, hform g, epsEq F c₀ c g, ← map_zpow]
    rfl
  · obtain ⟨a, ha, hZ⟩ := spanO c F.G₀ (mat ρ₀) (by
      have : (fun g => (mat ρ₀ g).map (algebraMap c.O (Qbar l))) = fun g => mat ρ g := funext hmρ
      rw [this]
      exact hspan)
    exact ⟨a, ha, hZ⟩
  · intro u g hg
    apply injG ι hι
    rw [hρx, map_one, hine u g hg]
  · intro v g
    refine ⟨fun i j hij => hz0 _ _ (hcM v g) i j ((hord v g).1 i j hij), fun i => ?_⟩
    apply hι
    rw [heq _ _ (hcM v g) i i, (hord v g).2.1 i]
    exact (congrArg Units.val (hψx v i g)).symm
  · intro v
    obtain ⟨g, hg⟩ := hreg v
    refine ⟨g, fun i j hij => hg ?_⟩
    show ψ v i g = ψ v j g
    rw [← hψx v i g, ← hψx v j g]
    exact congrArg _ hij
  · intro v i j hij hE
    apply hN1 v i j hij
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply, ← hψx v i g, ← hψx v j g, epsEq F c₀ c, hE]
    rfl
  · refine ⟨fun i j => ?_, fun g g' => ?_, fun g => ?_, fun u g hg => ?_, fun v => ⟨Y₀ v, fun g => ⟨?_, ?_, ?_, ?_⟩⟩⟩
    · apply hcont
      have : (fun g => ι (z₀ g i j)) = fun g => z g i j := by
        funext g
        exact heq _ _ (hmz g) i j
      rw [this]
      exact hz.cont.matrix_elem i j
    · apply injM ι hι
      show ι.mapMatrix (z₀ (g * g')) = ι.mapMatrix (z₀ g + mat ρ₀ g * z₀ g' * mat ρ₀ g⁻¹)
      rw [map_add, map_mul, map_mul, hmz, hmz, hmz, hmρ, hmρ, hz.coc]
    · apply injM ι hι
      show ι.mapMatrix ((P₀ : Matrix (Fin n) (Fin n) c.O) * z₀ (F.conj g)) = ι.mapMatrix (-((z₀ g)ᵀ * (P₀ : Matrix (Fin n) (Fin n) c.O)))
      rw [map_mul, map_neg, map_mul, mapT, hmP, hmz, hmz, hz.pol]
    · apply injM ι hι
      rw [hmz, map_zero, hz.ine u g hg]
    · exact fun i j hij => hz0 _ _ (hcM v g) i j ((hord v g).1 i j hij)
    · intro i
      apply hι
      rw [heq _ _ (hcM v g) i i, (hord v g).2.1 i]
      exact (congrArg Units.val (hψx v i g)).symm
    · exact fun i j hij => hz0 _ _ (hbig v _) i j ((hord v g).2.2.1 i j hij)
    · exact fun hg i => hz0 _ _ (hbig v _) i i ((hord v g).2.2.2 hg i)
