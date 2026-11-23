import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem map_algebraMap_mul_mul_map_linearMap {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) {Y Z : Type} [CommRing Y] [Algebra x.A Y] [CommRing Z] [Algebra x.A Z] (u : Y →ₗ[x.A] Z) (P Q : Matrix (Fin n) (Fin n) x.A) (N : Matrix (Fin n) (Fin n) Y) :
    (P.map (algebraMap x.A Y) * N * Q.map (algebraMap x.A Y)).map u = P.map (algebraMap x.A Z) * N.map u * Q.map (algebraMap x.A Z) := by
  have key : ∀ (p q : x.A) (y : Y), u (algebraMap x.A Y p * y * algebraMap x.A Y q) = algebraMap x.A Z p * u y * algebraMap x.A Z q := by
    intro p q y
    have h1 : algebraMap x.A Y p * y * algebraMap x.A Y q = (p * q) • y := by
      rw [Algebra.smul_def, map_mul]; ring
    have h2 : algebraMap x.A Z p * u y * algebraMap x.A Z q = (p * q) • u y := by
      rw [Algebra.smul_def, map_mul]; ring
    rw [h1, h2, map_smul]
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Finset.sum_mul, map_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => key _ _ _

private theorem exists_matrix_map_eq_of_zero_on_of_mem_range {n : ℕ} {R Y Z : Type} [CommRing R] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z] (w : Y →ₗ[R] Z) (S : Fin n → Fin n → Prop) (N : Matrix (Fin n) (Fin n) Z) (h0 : ∀ i j, S i j → N i j = 0) (hr : ∀ i j, ¬ S i j → N i j ∈ Set.range w) :
    ∃ N' : Matrix (Fin n) (Fin n) Y, (∀ i j, S i j → N' i j = 0) ∧ N'.map w = N := by
  classical
  refine ⟨Matrix.of fun i j => if h : S i j then 0 else (hr i j h).choose, ?_, ?_⟩
  · intro i j hij
    simp [hij]
  · ext i j
    by_cases hij : S i j
    · simp [hij, h0 i j hij]
    · simp [hij, (hr i j hij).choose_spec]

private theorem mem_od_iff_entry_eq_zero_of_same_block {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ} (N : Matrix (Fin n) (Fin n) R) :
    N ∈ Od A R n a ↔ ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) → N i j = 0 := by
  constructor
  · intro hN i j hij
    exact (Submodule.mem_bot _).1 ((hN i j).1 hij)
  · intro hN i j
    exact ⟨fun hij => (Submodule.mem_bot _).2 (hN i j hij), fun _ => Submodule.mem_top⟩

private theorem inv_w_entry_eq_zero_of_ty_ne_lt_a {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) (j k : Fin n) (hjk : x.ty v j ≠ decide ((k : ℕ) < x.a)) :
    (((x.w v)⁻¹ : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K)) j k = 0 := by
  classical
  set W : Matrix (Fin n) (Fin n) (PowerSeries x.K) := ((x.w v : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K)) with hW
  set B : Matrix (Fin n) (Fin n) (PowerSeries x.K) := (((x.w v)⁻¹ : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K)) with hB
  have hBW : B * W = 1 := Units.inv_mul (x.w v)
  have hWB : W * B = 1 := Units.mul_inv (x.w v)
  let β : Bool → PowerSeries x.K := fun b => if b then 1 else 0
  have hpat : W * Matrix.diagonal (fun j : Fin n => β (x.ty v j)) = Matrix.diagonal (fun i : Fin n => β (decide ((i : ℕ) < x.a))) * W := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases h : decide ((i : ℕ) < x.a) = x.ty v j
    · rw [h]; ring_nf
    · rw [show W i j = 0 from x.w_blk v i j h]; simp
  have key : Matrix.diagonal (fun j : Fin n => β (x.ty v j)) * B = B * Matrix.diagonal (fun i : Fin n => β (decide ((i : ℕ) < x.a))) := by
    calc Matrix.diagonal (fun j : Fin n => β (x.ty v j)) * B = B * W * Matrix.diagonal (fun j : Fin n => β (x.ty v j)) * B := by
          rw [hBW, Matrix.one_mul]
      _ = B * (W * Matrix.diagonal (fun j : Fin n => β (x.ty v j))) * B := by rw [Matrix.mul_assoc B]
      _ = B * Matrix.diagonal (fun i : Fin n => β (decide ((i : ℕ) < x.a))) * (W * B) := by
          rw [hpat]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hWB, Matrix.mul_one]
  have e := congrArg (fun M : Matrix (Fin n) (Fin n) (PowerSeries x.K) => M j k) key
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at e
  change B j k = 0
  cases h1 : x.ty v j <;> cases h2 : decide ((k : ℕ) < x.a) <;> simp only [h1, h2, β] at e hjk <;> simp_all

private theorem wiX_mul_mul_wX_eq_zero_of_ty_eq {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) {Y : Type} [CommRing Y] [Algebra x.A Y] (N : Matrix (Fin n) (Fin n) Y) (hN : ∀ k l : Fin n, ((k : ℕ) < x.a ↔ (l : ℕ) < x.a) → N k l = 0) (i j : Fin n) (hij : x.ty v i = x.ty v j) :
    (x.wiX Y v * N * x.wX Y v) i j = 0 := by
  simp only [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h1 : x.ty v i = decide ((k : ℕ) < x.a)
  · by_cases h2 : decide ((l : ℕ) < x.a) = x.ty v j
    · rw [hN k l (decide_eq_decide.mp (by rw [← h1, hij, ← h2]))]; simp
    · simp [NP.wX, x.w_blk v l j h2]
  · simp only [NP.wiX, Matrix.map_apply]
    rw [inv_w_entry_eq_zero_of_ty_ne_lt_a x v i k h1]; simp

private theorem wX_mul_mul_wiX_eq_zero_of_same_block {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) {Y : Type} [CommRing Y] [Algebra x.A Y] (P : Matrix (Fin n) (Fin n) Y) (hP : ∀ k l : Fin n, x.ty v k = x.ty v l → P k l = 0) (i j : Fin n) (hij : ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)) :
    (x.wX Y v * P * x.wiX Y v) i j = 0 := by
  simp only [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h1 : decide ((i : ℕ) < x.a) = x.ty v k
  · by_cases h2 : x.ty v l = decide ((j : ℕ) < x.a)
    · rw [hP k l (by rw [← h1, h2]; exact decide_eq_decide.mpr hij)]; simp
    · simp only [NP.wiX, Matrix.map_apply]
      rw [inv_w_entry_eq_zero_of_ty_ne_lt_a x v l j h2]; simp
  · simp [NP.wX, x.w_blk v i k h1]

private theorem map_wiX_mul_mul_wX_and_wX_mul_mul_wiX {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) {Y Z : Type} [CommRing Y] [Algebra x.A Y] [CommRing Z] [Algebra x.A Z] (u : Y →ₗ[x.A] Z) (N : Matrix (Fin n) (Fin n) Y) :
    (x.wiX Y v * N * x.wX Y v).map u = x.wiX Z v * N.map u * x.wX Z v ∧
      (x.wX Y v * N * x.wiX Y v).map u = x.wX Z v * N.map u * x.wiX Z v := by
  unfold NP.wX NP.wiX
  exact ⟨map_algebraMap_mul_mul_map_linearMap x u _ _ N, map_algebraMap_mul_mul_map_linearMap x u _ _ N⟩

private theorem wiX_mul_wX_eq_one_and_wX_mul_wiX_eq_one {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) {Y : Type} [CommRing Y] [Algebra x.A Y] :
    x.wiX Y v * x.wX Y v = 1 ∧ x.wX Y v * x.wiX Y v = 1 := by
  unfold NP.wX NP.wiX
  constructor
  · rw [← Matrix.map_mul, Units.inv_mul]; simp
  · rw [← Matrix.map_mul, Units.mul_inv]; simp

theorem UpperTheory.V.Pa.B2.odSES :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X' : Type) [CommRing X'] [Algebra x.A X'] (X : Type) [CommRing X] [Algebra x.A X] (X'' : Type) [CommRing X''] [Algebra x.A X''] (D' D D'' : Dat x.A (plOf G)) (o' : IsOd h x X' D') (o : IsOd h x X D) (o'' : IsOd h x X'' D'') (u : X' →ₗ[x.A] X) (v : X →ₗ[x.A] X'') (f : D'.Hom D) (g : D.Hom D''), Induced o' o u f → Induced o o'' v g → Function.Injective u → Function.Exact u v → Function.Surjective v → Dat.SES f g := by
  intro l _ L G G0 h n x X' _ _ X _ _ X'' _ _ D' D D'' o' o o'' u v f g hf hg hu hex hv
  have inj : Function.Injective f.f := by
    intro m1 m2 h12
    apply o'.e.injective
    apply Subtype.ext
    have e1 := hf m1
    rw [h12, hf m2] at e1
    ext i j
    exact hu (by simpa using congrArg (fun M : Matrix (Fin n) (Fin n) X => M i j) e1.symm)
  have ex : Function.Exact f.f g.f := by
    intro m
    constructor
    · intro hgm
      have h0 : (↑(o.e m) : Matrix (Fin n) (Fin n) X).map v = 0 := by
        rw [← hg m, hgm]; simp
      obtain ⟨N', hN'0, hN'⟩ := exists_matrix_map_eq_of_zero_on_of_mem_range u (fun i j : Fin n => ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)) (↑(o.e m))
        (fun i j hij => (mem_od_iff_entry_eq_zero_of_same_block _).1 (o.e m).2 i j hij)
        (fun i j _ => (hex _).1 (by simpa using congrArg (fun M : Matrix (Fin n) (Fin n) X'' => M i j) h0))
      refine ⟨o'.e.symm ⟨N', (mem_od_iff_entry_eq_zero_of_same_block _).2 hN'0⟩, ?_⟩
      apply o.e.injective
      apply Subtype.ext
      rw [hf, LinearEquiv.apply_symm_apply]
      exact hN'
    · rintro ⟨m', rfl⟩
      apply o''.e.injective
      apply Subtype.ext
      rw [hg, hf, map_zero]
      ext i j
      simpa using (hex _).2 ⟨_, rfl⟩
  have surj : Function.Surjective g.f := by
    intro m''
    obtain ⟨N, hN0, hN⟩ := exists_matrix_map_eq_of_zero_on_of_mem_range v (fun i j : Fin n => ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)) (↑(o''.e m''))
      (fun i j hij => (mem_od_iff_entry_eq_zero_of_same_block _).1 (o''.e m'').2 i j hij) (fun i j _ => hv _)
    refine ⟨o.e.symm ⟨N, (mem_od_iff_entry_eq_zero_of_same_block _).2 hN0⟩, ?_⟩
    apply o''.e.injective
    apply Subtype.ext
    rw [hg, LinearEquiv.apply_symm_apply]
    exact hN
  refine ⟨inj, ex, surj, ?_, ?_⟩
  · intro w
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨m, rfl⟩ := D'.surj w q
    rw [f.comm] at hq
    rcases w with w | w
    · rw [o'.kerV]
      rw [o.kerV] at hq
      intro i j hji
      have e := hq i j hji
      rw [hf, ← (map_wiX_mul_mul_wX_and_wX_mul_mul_wiX x w u _).1, Matrix.map_apply] at e
      exact hu (by rw [map_zero]; exact e)
    · have h1 : f.f m = 0 := o.kerU w (by rw [hq, map_zero])
      rw [inj (h1.trans (map_zero f.f).symm), map_zero]
  · intro w q
    constructor
    · intro hq
      obtain ⟨m, rfl⟩ := D.surj w q
      rw [g.comm] at hq
      rcases w with w | w
      · have hlow := (o''.kerV w (g.f m)).1 hq
        obtain ⟨P, hP0, hP⟩ := exists_matrix_map_eq_of_zero_on_of_mem_range v (fun i j : Fin n => j < i ∨ x.ty w i = x.ty w j)
          (x.wiX X'' w * (↑(o''.e (g.f m)) : Matrix (Fin n) (Fin n) X'') * x.wX X'' w)
          (fun i j hij => hij.elim (hlow i j) (wiX_mul_mul_wX_eq_zero_of_ty_eq x w _ ((mem_od_iff_entry_eq_zero_of_same_block _).1 (o''.e (g.f m)).2) i j))
          (fun i j _ => hv _)
        have hN : x.wX X w * P * x.wiX X w ∈ Od x.A X n x.a :=
          (mem_od_iff_entry_eq_zero_of_same_block _).2 (fun i j hij => wX_mul_mul_wiX_eq_zero_of_same_block x w P (fun k l hkl => hP0 k l (Or.inr hkl)) i j hij)
        obtain ⟨h1, h2⟩ := wiX_mul_wX_eq_one_and_wX_mul_wiX_eq_one x w (Y := X)
        obtain ⟨h1'', h2''⟩ := wiX_mul_wX_eq_one_and_wX_mul_wiX_eq_one x w (Y := X'')
        have hconj : x.wiX X w * (↑(o.e (o.e.symm ⟨_, hN⟩)) : Matrix (Fin n) (Fin n) X) * x.wX X w = P := by
          rw [LinearEquiv.apply_symm_apply]
          show x.wiX X w * (x.wX X w * P * x.wiX X w) * x.wX X w = P
          simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
        have hk : D.π (Sum.inl w) (o.e.symm ⟨_, hN⟩) = 0 :=
          (o.kerV w _).2 (fun i j hji => by rw [hconj]; exact hP0 i j (Or.inl hji))
        have hg0 : g.f (o.e.symm ⟨_, hN⟩) = g.f m := by
          apply o''.e.injective
          apply Subtype.ext
          rw [hg (o.e.symm ⟨_, hN⟩), LinearEquiv.apply_symm_apply]
          show (x.wX X w * P * x.wiX X w).map v = _
          rw [(map_wiX_mul_mul_wX_and_wX_mul_mul_wiX x w v P).2, hP]
          simp only [Matrix.mul_assoc, h2'', Matrix.mul_one]
          rw [← Matrix.mul_assoc, h2'', Matrix.one_mul]
        have hdiff : g.f (m - o.e.symm ⟨_, hN⟩) = 0 := by rw [map_sub, hg0, sub_self]
        obtain ⟨m', hm'⟩ := (ex _).1 hdiff
        refine ⟨D'.π _ m', (f.comm _ m').trans ?_⟩
        rw [hm', map_sub, hk, sub_zero]
      · have h1 : g.f m = 0 := o''.kerU w (by rw [hq, map_zero])
        obtain ⟨m', hm'⟩ := (ex m).1 h1
        exact ⟨D'.π _ m', (f.comm _ m').trans (congrArg _ hm')⟩
    · rintro ⟨q', rfl⟩
      obtain ⟨m', rfl⟩ := D'.surj w q'
      rw [f.comm, g.comm, (ex (f.f m')).2 ⟨m', rfl⟩, map_zero]
