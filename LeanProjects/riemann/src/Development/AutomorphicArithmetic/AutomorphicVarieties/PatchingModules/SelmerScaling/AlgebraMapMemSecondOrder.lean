import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa.SelmerFractionFieldBaseChange

variable {l : ℕ} [Fact l.Prime] {Fm : GFrame l} {n : ℕ} {x : NP Fm n} (k : Kap x) (F : Type) [CommRing F] [Algebra x.A F]

end UpperTheory.V.Pa.SelmerFractionFieldBaseChange

private theorem selMap2_lemma {R S Γ : Type} [CommRing R] [CommRing S] [TopologicalSpace Γ] (I : Ideal R) (J : Ideal S)
    (π : R →+ S) (hπ : ∀ N u, u ∈ I ^ N → π u ∈ J ^ N) (f : Γ → R) (hf : AdicCont I f) :
    AdicCont J (fun g => π (f g)) := by
  intro N
  have hs := Ideal.Quotient.mk_surjective (I := I ^ N)
  have e : (fun g => Ideal.Quotient.mk (J ^ N) (π (f g))) =
      (fun q => Ideal.Quotient.mk (J ^ N) (π (Function.surjInv hs q))) ∘
        (fun g => Ideal.Quotient.mk (I ^ N) (f g)) := by
    funext g
    simp only [Function.comp]
    rw [Ideal.Quotient.eq, ← map_sub]
    apply hπ
    rw [← Ideal.Quotient.eq]
    exact (Function.surjInv_eq hs _).symm
  rw [e]
  exact (hf N).comp _

private theorem dd_components_mem_span_pow_of_mem_span_algebraMap_pow {A : Type} [CommRing A] (g : ℕ) (t : A) (N : ℕ) (u : DD A g)
    (hu : u ∈ Ideal.span {algebraMap A (DD A g) t} ^ N) :
    u.a ∈ Ideal.span {t} ^ N ∧ (∀ j, u.ep j ∈ Ideal.span {t} ^ N) ∧ (∀ j, u.ep' j ∈ Ideal.span {t} ^ N) ∧
      u.eta ∈ Ideal.span {t} ^ N := by
  rw [Ideal.span_singleton_pow, ← map_pow, Ideal.mem_span_singleton'] at hu
  obtain ⟨r, rfl⟩ := hu
  rw [Ideal.span_singleton_pow]
  have ha : (algebraMap A (DD A g) (t ^ N)).a = t ^ N := rfl
  have he : (algebraMap A (DD A g) (t ^ N)).ep = 0 := rfl
  have he' : (algebraMap A (DD A g) (t ^ N)).ep' = 0 := rfl
  have hη : (algebraMap A (DD A g) (t ^ N)).eta = 0 := rfl
  refine ⟨?_, fun j => ?_, fun j => ?_, ?_⟩
  · rw [DD.mul_a, ha]
    exact Ideal.mem_span_singleton'.mpr ⟨r.a, rfl⟩
  · rw [DD.mul_ep, ha, he]
    exact Ideal.mem_span_singleton'.mpr ⟨r.ep j, by simp⟩
  · rw [DD.mul_ep', ha, he']
    exact Ideal.mem_span_singleton'.mpr ⟨r.ep' j, by simp⟩
  · rw [DD.mul_eta, ha, he, he', hη]
    exact Ideal.mem_span_singleton'.mpr ⟨r.eta, by simp⟩

private theorem dd_map_algebraMap_algebraMap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (g : ℕ) (c : A) :
    DD.map (algebraMap A B) (algebraMap A (DD A g) c) = algebraMap A (DD B g) c :=
  DD.ext rfl (funext fun _ => map_zero _) (funext fun _ => map_zero _) (map_zero _)

private theorem dd_map_mem_span_algebraMap_pow {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (g : ℕ) (t : A) (N : ℕ) (u : DD A g)
    (hu : u ∈ Ideal.span {algebraMap A (DD A g) t} ^ N) :
    DD.map (algebraMap A B) u ∈ Ideal.span {algebraMap A (DD B g) t} ^ N := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hu ⊢
  obtain ⟨r, rfl⟩ := hu
  exact ⟨DD.map (algebraMap A B) r, by rw [map_mul, map_pow, dd_map_algebraMap_algebraMap]⟩

private theorem ddMap_algebraMap_mem_ddPart {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (g : ℕ) (b1 b2 b3 b4 : Bool)
    (u : DD A g) (hu : u ∈ ddPart A A g b1 b2 b3 b4) : DD.map (algebraMap A B) u ∈ ddPart A B g b1 b2 b3 b4 := by
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · show algebraMap A B u.a = 0
    rw [h1 h, map_zero]
  · show (fun j => algebraMap A B (u.ep j)) = 0
    rw [h2 h]
    funext j
    exact map_zero _
  · show (fun j => algebraMap A B (u.ep' j)) = 0
    rw [h3 h]
    funext j
    exact map_zero _
  · show algebraMap A B u.eta = 0
    rw [h4 h, map_zero]

private theorem map_ddMap_algebraMap_mem_W2 {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (n g a : ℕ)
    (Z : Matrix (Fin n) (Fin n) (DD A g)) (hZ : Z ∈ W2 n A A g a) :
    Z.map (DD.map (algebraMap A B)) ∈ W2 n A B g a := by
  intro i j
  exact ⟨fun hc => ddMap_algebraMap_mem_ddPart g _ _ _ _ _ ((hZ i j).1 hc), fun hc => ddMap_algebraMap_mem_ddPart g _ _ _ _ _ ((hZ i j).2 hc)⟩

private theorem map_algebraMap_map_ddMap_algebraMap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (n g : ℕ)
    (M : Matrix (Fin n) (Fin n) A) :
    (M.map (algebraMap A (DD A g))).map (DD.map (algebraMap A B)) = M.map (algebraMap A (DD B g)) := by
  exact Matrix.ext fun i j => dd_map_algebraMap_algebraMap (A := A) (B := B) g (M i j)

private theorem epM_map_ddMap_algebraMap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (n g : ℕ)
    (Z : Fin g → Matrix (Fin n) (Fin n) A) :
    (DD.epM Z).map (DD.map (algebraMap A B)) = DD.epM (fun j => (Z j).map (algebraMap A B)) := by
  refine Matrix.ext fun i j => DD.ext ?_ ?_ ?_ ?_
  · exact map_zero (algebraMap A B)
  · rfl
  · funext m
    exact map_zero (algebraMap A B)
  · exact map_zero (algebraMap A B)

private theorem kap_rho1_map_ddMap_algebraMap {l : ℕ} [Fact l.Prime] {Fm : GFrame l} {n : ℕ} {x : NP Fm n} (k : Kap x) (B : Type)
    [CommRing B] [Algebra x.A B] (g : Fm.G₀) :
    (k.ρ1 x.A g).map (DD.map (algebraMap x.A B)) = k.ρ1 B g := by
  have e : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g),
      M.map (DD.map (algebraMap x.A B)) = (DD.map (algebraMap x.A B)).mapMatrix M := fun _ => rfl
  unfold Kap.ρ1 NP.ρX
  rw [e, map_mul, map_add, map_one, ← e, ← e, epM_map_ddMap_algebraMap, map_algebraMap_map_ddMap_algebraMap]
  rfl

private theorem w1_map_dd_map_algebraMap {l : ℕ} [Fact l.Prime] {Fm : GFrame l} {n : ℕ} {x : NP Fm n} (k : Kap x) (B : Type)
    [CommRing B] [Algebra x.A B] (v : Fm.Vl) :
    (k.w1 x.A v).map (DD.map (algebraMap x.A B)) = k.w1 B v := by
  have e : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g),
      M.map (DD.map (algebraMap x.A B)) = (DD.map (algebraMap x.A B)).mapMatrix M := fun _ => rfl
  unfold Kap.w1 NP.wX
  rw [e, map_mul, map_sub, map_one, ← e, ← e, epM_map_ddMap_algebraMap, map_algebraMap_map_ddMap_algebraMap]
  rfl

private theorem wi1_map_dd_map_algebraMap {l : ℕ} [Fact l.Prime] {Fm : GFrame l} {n : ℕ} {x : NP Fm n} (k : Kap x) (B : Type)
    [CommRing B] [Algebra x.A B] (v : Fm.Vl) :
    (k.wi1 x.A v).map (DD.map (algebraMap x.A B)) = k.wi1 B v := by
  have e : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g),
      M.map (DD.map (algebraMap x.A B)) = (DD.map (algebraMap x.A B)).mapMatrix M := fun _ => rfl
  unfold Kap.wi1 NP.wiX
  rw [e, map_mul, map_add, map_one, ← e, ← e, epM_map_ddMap_algebraMap, map_algebraMap_map_ddMap_algebraMap]
  rfl

private theorem selMap2_lemma_12 {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) {R S : Type} [CommRing R] [CommRing S]
    (Φ : R →+* S) (ρ z : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R)
    (ρ' z' : F.G₀ → Matrix (Fin n) (Fin n) S) (w' wi' : F.Vl → Matrix (Fin n) (Fin n) S)
    (hρ : ∀ g, ρ' g = (ρ g).map Φ) (hz : ∀ g, z' g = (z g).map Φ) (hw : ∀ v, w' v = (w v).map Φ)
    (hwi : ∀ v, wi' v = (wi v).map Φ) (v : F.Vl) (Y : Matrix (Fin n) (Fin n) R)
    (hL : LocAt F ρ w wi z v Y) : LocAt F ρ' w' wi' z' v (Y.map Φ) := by
  have eM : ∀ M : Matrix (Fin n) (Fin n) R, M.map Φ = Φ.mapMatrix M := fun _ => rfl
  intro g
  obtain ⟨h1, h2⟩ := hL g
  have e : wi' v * (z' (F.φ v g) - dY F ρ' (Y.map Φ) (F.φ v g)) * w' v =
      (wi v * (z (F.φ v g) - dY F ρ Y (F.φ v g)) * w v).map Φ := by
    simp only [dY, hρ, hz, hw, hwi, eM, map_mul, map_sub]
  refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
  · rw [e, Matrix.map_apply, h1 i j hij, map_zero]
  · rw [e, Matrix.map_apply, h2 hg i, map_zero]

open UpperTheory.V.Pa.SelmerFractionFieldBaseChange in
theorem UpperTheory.V.Pa.selMap2 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ z ∈ Sel2 h x.A k, (fun g => (z g).map (DD.map (algebraMap x.A x.Fr))) ∈ Sel2 h x.Fr k ∧ BndD x.t fun g => (z g).map (DD.map (algebraMap x.A x.Fr)) := by
  intro l _ L G G0 h n x k z hz
  obtain ⟨hV, hC, hco, hcj, hIu, hloc⟩ := hz
  have eM : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g),
      M.map (DD.map (algebraMap x.A x.Fr)) = (DD.map (algebraMap x.A x.Fr)).mapMatrix M := fun _ => rfl
  refine ⟨⟨fun g => map_ddMap_algebraMap_mem_W2 n k.g x.a _ (hV g), fun i j => ?_, fun g1 g2 => ?_, fun g => ?_,
    fun u g hg => ?_, fun v => ?_⟩, fun i j => ⟨?_, fun m => ?_, fun m => ?_, ?_⟩⟩
  · exact selMap2_lemma _ _ (DD.map (algebraMap x.A x.Fr)).toAddMonoidHom
      (fun N u hu => dd_map_mem_span_algebraMap_pow k.g x.t N u hu) (fun g => z g i j) (hC i j)
  · beta_reduce
    beta_reduce at hco
    rw [hco g1 g2, ← kap_rho1_map_ddMap_algebraMap k x.Fr, ← kap_rho1_map_ddMap_algebraMap k x.Fr]
    simp only [eM, map_add, map_mul]
  · beta_reduce
    rw [hcj g]
    exact Matrix.ext fun i j => map_neg (DD.map (algebraMap x.A x.Fr)) (z g j i)
  · beta_reduce
    rw [hIu u g hg]
    exact Matrix.map_zero _ (map_zero _)
  · obtain ⟨Y, hY, hL⟩ := hloc v
    exact ⟨Y.map (DD.map (algebraMap x.A x.Fr)), map_ddMap_algebraMap_mem_W2 n k.g x.a _ hY,
      selMap2_lemma_12 G.frame (DD.map (algebraMap x.A x.Fr)) _ z _ _ _ _ _ _
        (fun g => (kap_rho1_map_ddMap_algebraMap k x.Fr _).symm) (fun g => rfl) (fun v => (w1_map_dd_map_algebraMap k x.Fr v).symm)
        (fun v => (wi1_map_dd_map_algebraMap k x.Fr v).symm) v Y hL⟩
  · refine ⟨0, fun g => (z g i j).a, ?_, fun g => by rw [pow_zero, one_mul]; rfl⟩
    exact selMap2_lemma _ _ { toFun := fun u : DD x.A k.g => u.a, map_zero' := rfl, map_add' := fun _ _ => rfl }
      (fun N u hu => (dd_components_mem_span_pow_of_mem_span_algebraMap_pow k.g x.t N u hu).1) (fun g => z g i j) (hC i j)
  · refine ⟨0, fun g => (z g i j).ep m, ?_, fun g => by rw [pow_zero, one_mul]; rfl⟩
    exact selMap2_lemma _ _ { toFun := fun u : DD x.A k.g => u.ep m, map_zero' := rfl, map_add' := fun _ _ => rfl }
      (fun N u hu => (dd_components_mem_span_pow_of_mem_span_algebraMap_pow k.g x.t N u hu).2.1 m) (fun g => z g i j) (hC i j)
  · refine ⟨0, fun g => (z g i j).ep' m, ?_, fun g => by rw [pow_zero, one_mul]; rfl⟩
    exact selMap2_lemma _ _ { toFun := fun u : DD x.A k.g => u.ep' m, map_zero' := rfl, map_add' := fun _ _ => rfl }
      (fun N u hu => (dd_components_mem_span_pow_of_mem_span_algebraMap_pow k.g x.t N u hu).2.2.1 m) (fun g => z g i j) (hC i j)
  · refine ⟨0, fun g => (z g i j).eta, ?_, fun g => by rw [pow_zero, one_mul]; rfl⟩
    exact selMap2_lemma _ _ { toFun := fun u : DD x.A k.g => u.eta, map_zero' := rfl, map_add' := fun _ _ => rfl }
      (fun N u hu => (dd_components_mem_span_pow_of_mem_span_algebraMap_pow k.g x.t N u hu).2.2.2) (fun g => z g i j) (hC i j)
